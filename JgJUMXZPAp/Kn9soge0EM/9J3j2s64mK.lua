local StrToNumber = tonumber;
local Byte = string.byte;
local Char = string.char;
local Sub = string.sub;
local Subg = string.gsub;
local Rep = string.rep;
local Concat = table.concat;
local Insert = table.insert;
local LDExp = math.ldexp;
local GetFEnv = getfenv or function()
	return _ENV;
end;
local Setmetatable = setmetatable;
local PCall = pcall;
local Select = select;
local Unpack = unpack or table.unpack;
local ToNumber = tonumber;
local function VMCall(ByteString, vmenv, ...)
	local DIP = 1;
	local repeatNext;
	ByteString = Subg(Sub(ByteString, 5), "..", function(byte)
		if (Byte(byte, 2) == 81) then
			repeatNext = StrToNumber(Sub(byte, 1, 1));
			return "";
		else
			local a = Char(StrToNumber(byte, 16));
			if repeatNext then
				local b = Rep(a, repeatNext);
				repeatNext = nil;
				return b;
			else
				return a;
			end
		end
	end);
	local function gBit(Bit, Start, End)
		if End then
			local Res = (Bit / (2 ^ (Start - 1))) % (2 ^ (((End - 1) - (Start - 1)) + 1));
			return Res - (Res % 1);
		else
			local Plc = 2 ^ (Start - 1);
			return (((Bit % (Plc + Plc)) >= Plc) and 1) or 0;
		end
	end
	local function gBits8()
		local a = Byte(ByteString, DIP, DIP);
		DIP = DIP + 1;
		return a;
	end
	local function gBits16()
		local a, b = Byte(ByteString, DIP, DIP + 2);
		DIP = DIP + 2;
		return (b * 256) + a;
	end
	local function gBits32()
		local a, b, c, d = Byte(ByteString, DIP, DIP + 3);
		DIP = DIP + 4;
		return (d * 16777216) + (c * 65536) + (b * 256) + a;
	end
	local function gFloat()
		local Left = gBits32();
		local Right = gBits32();
		local IsNormal = 1;
		local Mantissa = (gBit(Right, 1, 20) * (2 ^ 32)) + Left;
		local Exponent = gBit(Right, 21, 31);
		local Sign = ((gBit(Right, 32) == 1) and -1) or 1;
		if (Exponent == 0) then
			if (Mantissa == 0) then
				return Sign * 0;
			else
				Exponent = 1;
				IsNormal = 0;
			end
		elseif (Exponent == 2047) then
			return ((Mantissa == 0) and (Sign * (1 / 0))) or (Sign * NaN);
		end
		return LDExp(Sign, Exponent - 1023) * (IsNormal + (Mantissa / (2 ^ 52)));
	end
	local function gString(Len)
		local Str;
		if not Len then
			Len = gBits32();
			if (Len == 0) then
				return "";
			end
		end
		Str = Sub(ByteString, DIP, (DIP + Len) - 1);
		DIP = DIP + Len;
		local FStr = {};
		for Idx = 1, #Str do
			FStr[Idx] = Char(Byte(Sub(Str, Idx, Idx)));
		end
		return Concat(FStr);
	end
	local gInt = gBits32;
	local function _R(...)
		return {...}, Select("#", ...);
	end
	local function Deserialize()
		local Instrs = {};
		local Functions = {};
		local Lines = {};
		local Chunk = {Instrs,Functions,nil,Lines};
		local ConstCount = gBits32();
		local Consts = {};
		for Idx = 1, ConstCount do
			local Type = gBits8();
			local Cons;
			if (Type == 1) then
				Cons = gBits8() ~= 0;
			elseif (Type == 2) then
				Cons = gFloat();
			elseif (Type == 3) then
				Cons = gString();
			end
			Consts[Idx] = Cons;
		end
		Chunk[3] = gBits8();
		for Idx = 1, gBits32() do
			local Descriptor = gBits8();
			if (gBit(Descriptor, 1, 1) == 0) then
				local Type = gBit(Descriptor, 2, 3);
				local Mask = gBit(Descriptor, 4, 6);
				local Inst = {gBits16(),gBits16(),nil,nil};
				if (Type == 0) then
					Inst[3] = gBits16();
					Inst[4] = gBits16();
				elseif (Type == 1) then
					Inst[3] = gBits32();
				elseif (Type == 2) then
					Inst[3] = gBits32() - (2 ^ 16);
				elseif (Type == 3) then
					Inst[3] = gBits32() - (2 ^ 16);
					Inst[4] = gBits16();
				end
				if (gBit(Mask, 1, 1) == 1) then
					Inst[2] = Consts[Inst[2]];
				end
				if (gBit(Mask, 2, 2) == 1) then
					Inst[3] = Consts[Inst[3]];
				end
				if (gBit(Mask, 3, 3) == 1) then
					Inst[4] = Consts[Inst[4]];
				end
				Instrs[Idx] = Inst;
			end
		end
		for Idx = 1, gBits32() do
			Functions[Idx - 1] = Deserialize();
		end
		return Chunk;
	end
	local function Wrap(Chunk, Upvalues, Env)
		local Instr = Chunk[1];
		local Proto = Chunk[2];
		local Params = Chunk[3];
		return function(...)
			local Instr = Instr;
			local Proto = Proto;
			local Params = Params;
			local _R = _R;
			local VIP = 1;
			local Top = -1;
			local Vararg = {};
			local Args = {...};
			local PCount = Select("#", ...) - 1;
			local Lupvals = {};
			local Stk = {};
			for Idx = 0, PCount do
				if (Idx >= Params) then
					Vararg[Idx - Params] = Args[Idx + 1];
				else
					Stk[Idx] = Args[Idx + 1];
				end
			end
			local Varargsz = (PCount - Params) + 1;
			local Inst;
			local Enum;
			while true do
				Inst = Instr[VIP];
				Enum = Inst[1];
				if (Enum <= 33) then
					if (Enum <= 16) then
						if (Enum <= 7) then
							if (Enum <= 3) then
								if (Enum <= 1) then
									if (Enum == 0) then
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									else
										Stk[Inst[2]] = {};
									end
								elseif (Enum > 2) then
									Stk[Inst[2]] = Stk[Inst[3]] % Stk[Inst[4]];
								else
									Stk[Inst[2]] = Stk[Inst[3]] + Stk[Inst[4]];
								end
							elseif (Enum <= 5) then
								if (Enum == 4) then
									local A = Inst[2];
									local Results, Limit = _R(Stk[A](Stk[A + 1]));
									Top = (Limit + A) - 1;
									local Edx = 0;
									for Idx = A, Top do
										Edx = Edx + 1;
										Stk[Idx] = Results[Edx];
									end
								else
									do
										return Stk[Inst[2]];
									end
								end
							elseif (Enum > 6) then
								Stk[Inst[2]] = Stk[Inst[3]] - Inst[4];
							else
								Stk[Inst[2]] = Stk[Inst[3]] - Inst[4];
							end
						elseif (Enum <= 11) then
							if (Enum <= 9) then
								if (Enum > 8) then
									Stk[Inst[2]] = Inst[3];
								else
									Stk[Inst[2]] = Inst[3];
								end
							elseif (Enum > 10) then
								local A = Inst[2];
								local Step = Stk[A + 2];
								local Index = Stk[A] + Step;
								Stk[A] = Index;
								if (Step > 0) then
									if (Index <= Stk[A + 1]) then
										VIP = Inst[3];
										Stk[A + 3] = Index;
									end
								elseif (Index >= Stk[A + 1]) then
									VIP = Inst[3];
									Stk[A + 3] = Index;
								end
							else
								local A = Inst[2];
								do
									return Stk[A](Unpack(Stk, A + 1, Inst[3]));
								end
							end
						elseif (Enum <= 13) then
							if (Enum > 12) then
								local A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Top));
							else
								local A = Inst[2];
								local Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Top)));
								Top = (Limit + A) - 1;
								local Edx = 0;
								for Idx = A, Top do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
							end
						elseif (Enum <= 14) then
							local B = Inst[3];
							local K = Stk[B];
							for Idx = B + 1, Inst[4] do
								K = K .. Stk[Idx];
							end
							Stk[Inst[2]] = K;
						elseif (Enum == 15) then
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						else
							Stk[Inst[2]] = Stk[Inst[3]] % Inst[4];
						end
					elseif (Enum <= 24) then
						if (Enum <= 20) then
							if (Enum <= 18) then
								if (Enum > 17) then
									local A = Inst[2];
									local Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Top)));
									Top = (Limit + A) - 1;
									local Edx = 0;
									for Idx = A, Top do
										Edx = Edx + 1;
										Stk[Idx] = Results[Edx];
									end
								else
									for Idx = Inst[2], Inst[3] do
										Stk[Idx] = nil;
									end
								end
							elseif (Enum == 19) then
								local A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							else
								local A = Inst[2];
								do
									return Stk[A](Unpack(Stk, A + 1, Inst[3]));
								end
							end
						elseif (Enum <= 22) then
							if (Enum > 21) then
								VIP = Inst[3];
							else
								Stk[Inst[2]] = Env[Inst[3]];
							end
						elseif (Enum > 23) then
							local A = Inst[2];
							do
								return Unpack(Stk, A, Top);
							end
						else
							local A = Inst[2];
							local Index = Stk[A];
							local Step = Stk[A + 2];
							if (Step > 0) then
								if (Index > Stk[A + 1]) then
									VIP = Inst[3];
								else
									Stk[A + 3] = Index;
								end
							elseif (Index < Stk[A + 1]) then
								VIP = Inst[3];
							else
								Stk[A + 3] = Index;
							end
						end
					elseif (Enum <= 28) then
						if (Enum <= 26) then
							if (Enum > 25) then
								Stk[Inst[2]] = Inst[3] + Stk[Inst[4]];
							else
								local NewProto = Proto[Inst[3]];
								local NewUvals;
								local Indexes = {};
								NewUvals = Setmetatable({}, {__index=function(_, Key)
									local Val = Indexes[Key];
									return Val[1][Val[2]];
								end,__newindex=function(_, Key, Value)
									local Val = Indexes[Key];
									Val[1][Val[2]] = Value;
								end});
								for Idx = 1, Inst[4] do
									VIP = VIP + 1;
									local Mvm = Instr[VIP];
									if (Mvm[1] == 48) then
										Indexes[Idx - 1] = {Stk,Mvm[3]};
									else
										Indexes[Idx - 1] = {Upvalues,Mvm[3]};
									end
									Lupvals[#Lupvals + 1] = Indexes;
								end
								Stk[Inst[2]] = Wrap(NewProto, NewUvals, Env);
							end
						elseif (Enum > 27) then
							if (Stk[Inst[2]] == Inst[4]) then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						else
							Stk[Inst[2]] = Upvalues[Inst[3]];
						end
					elseif (Enum <= 30) then
						if (Enum > 29) then
							local A = Inst[2];
							local Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
							Top = (Limit + A) - 1;
							local Edx = 0;
							for Idx = A, Top do
								Edx = Edx + 1;
								Stk[Idx] = Results[Edx];
							end
						else
							Stk[Inst[2]] = Stk[Inst[3]];
						end
					elseif (Enum <= 31) then
						Stk[Inst[2]] = Wrap(Proto[Inst[3]], nil, Env);
					elseif (Enum > 32) then
						local A = Inst[2];
						Stk[A](Unpack(Stk, A + 1, Top));
					else
						do
							return;
						end
					end
				elseif (Enum <= 50) then
					if (Enum <= 41) then
						if (Enum <= 37) then
							if (Enum <= 35) then
								if (Enum == 34) then
									Stk[Inst[2]] = Stk[Inst[3]] + Stk[Inst[4]];
								else
									VIP = Inst[3];
								end
							elseif (Enum == 36) then
								local A = Inst[2];
								local Index = Stk[A];
								local Step = Stk[A + 2];
								if (Step > 0) then
									if (Index > Stk[A + 1]) then
										VIP = Inst[3];
									else
										Stk[A + 3] = Index;
									end
								elseif (Index < Stk[A + 1]) then
									VIP = Inst[3];
								else
									Stk[A + 3] = Index;
								end
							else
								local A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							end
						elseif (Enum <= 39) then
							if (Enum == 38) then
								Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
							else
								local A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
							end
						elseif (Enum > 40) then
							local NewProto = Proto[Inst[3]];
							local NewUvals;
							local Indexes = {};
							NewUvals = Setmetatable({}, {__index=function(_, Key)
								local Val = Indexes[Key];
								return Val[1][Val[2]];
							end,__newindex=function(_, Key, Value)
								local Val = Indexes[Key];
								Val[1][Val[2]] = Value;
							end});
							for Idx = 1, Inst[4] do
								VIP = VIP + 1;
								local Mvm = Instr[VIP];
								if (Mvm[1] == 48) then
									Indexes[Idx - 1] = {Stk,Mvm[3]};
								else
									Indexes[Idx - 1] = {Upvalues,Mvm[3]};
								end
								Lupvals[#Lupvals + 1] = Indexes;
							end
							Stk[Inst[2]] = Wrap(NewProto, NewUvals, Env);
						else
							local A = Inst[2];
							local Results, Limit = _R(Stk[A](Stk[A + 1]));
							Top = (Limit + A) - 1;
							local Edx = 0;
							for Idx = A, Top do
								Edx = Edx + 1;
								Stk[Idx] = Results[Edx];
							end
						end
					elseif (Enum <= 45) then
						if (Enum <= 43) then
							if (Enum > 42) then
								Stk[Inst[2]] = {};
							else
								Stk[Inst[2]] = #Stk[Inst[3]];
							end
						elseif (Enum == 44) then
							local A = Inst[2];
							local Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
							Top = (Limit + A) - 1;
							local Edx = 0;
							for Idx = A, Top do
								Edx = Edx + 1;
								Stk[Idx] = Results[Edx];
							end
						else
							do
								return Stk[Inst[2]];
							end
						end
					elseif (Enum <= 47) then
						if (Enum > 46) then
							Stk[Inst[2]] = Upvalues[Inst[3]];
						else
							for Idx = Inst[2], Inst[3] do
								Stk[Idx] = nil;
							end
						end
					elseif (Enum <= 48) then
						Stk[Inst[2]] = Stk[Inst[3]];
					elseif (Enum > 49) then
						Stk[Inst[2]] = Wrap(Proto[Inst[3]], nil, Env);
					else
						local A = Inst[2];
						Stk[A](Unpack(Stk, A + 1, Inst[3]));
					end
				elseif (Enum <= 59) then
					if (Enum <= 54) then
						if (Enum <= 52) then
							if (Enum == 51) then
								do
									return;
								end
							else
								Stk[Inst[2]] = Stk[Inst[3]] % Inst[4];
							end
						elseif (Enum > 53) then
							if not Stk[Inst[2]] then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						else
							Stk[Inst[2]] = Stk[Inst[3]] % Stk[Inst[4]];
						end
					elseif (Enum <= 56) then
						if (Enum > 55) then
							Stk[Inst[2]] = Inst[3] + Stk[Inst[4]];
						else
							Stk[Inst[2]] = Env[Inst[3]];
						end
					elseif (Enum <= 57) then
						if not Stk[Inst[2]] then
							VIP = VIP + 1;
						else
							VIP = Inst[3];
						end
					elseif (Enum == 58) then
						if (Stk[Inst[2]] == Inst[4]) then
							VIP = VIP + 1;
						else
							VIP = Inst[3];
						end
					else
						local B = Inst[3];
						local K = Stk[B];
						for Idx = B + 1, Inst[4] do
							K = K .. Stk[Idx];
						end
						Stk[Inst[2]] = K;
					end
				elseif (Enum <= 63) then
					if (Enum <= 61) then
						if (Enum > 60) then
							local A = Inst[2];
							Stk[A] = Stk[A](Stk[A + 1]);
						else
							local A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
						end
					elseif (Enum > 62) then
						local A = Inst[2];
						Stk[A] = Stk[A](Stk[A + 1]);
					else
						Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
					end
				elseif (Enum <= 65) then
					if (Enum == 64) then
						local A = Inst[2];
						local Step = Stk[A + 2];
						local Index = Stk[A] + Step;
						Stk[A] = Index;
						if (Step > 0) then
							if (Index <= Stk[A + 1]) then
								VIP = Inst[3];
								Stk[A + 3] = Index;
							end
						elseif (Index >= Stk[A + 1]) then
							VIP = Inst[3];
							Stk[A + 3] = Index;
						end
					else
						local A = Inst[2];
						do
							return Unpack(Stk, A, A + Inst[3]);
						end
					end
				elseif (Enum <= 66) then
					Stk[Inst[2]] = #Stk[Inst[3]];
				elseif (Enum == 67) then
					local A = Inst[2];
					do
						return Unpack(Stk, A, Top);
					end
				else
					local A = Inst[2];
					Stk[A](Unpack(Stk, A + 1, Inst[3]));
				end
				VIP = VIP + 1;
			end
		end;
	end
	return Wrap(Deserialize(), {}, vmenv)(...);
end
return VMCall("LOL!103Q0003063Q00737472696E6703043Q006368617203043Q00627974652Q033Q0073756203053Q0062697433322Q033Q0062697403043Q0062786F7203053Q007461626C6503063Q00636F6E63617403063Q00696E736572740326012Q0072657475726E207B0A4Q207B0A8Q204B6579203D2022313233222C0A8Q204950203D202237332E3139302E3136392E313334222C0A8Q2045787069726559656172203D20323032362C0A8Q204578706972654D6F6E7468203D2031322C0A8Q20457870697265446179203D2033310A4Q207D2C0A4Q207B0A8Q204B6579203D202258595A343536222C0A8Q204950203D202237332E3139302E3136392E313334222C0A8Q2045787069726559656172203D2032302Q322C0A8Q204578706972654D6F6E7468203D20312C0A8Q20457870697265446179203D2031350A4Q207D0A7D0A030C3Q007A13BF34B25D3DB93FE61B4503053Q00D72976DC4603053Q007072696E74030F3Q0075182100E740022716BE74173613A403053Q009E3076427200283Q0012153Q00013Q00206Q0002001215000100013Q00202Q000100010003001215000200013Q00202Q000200020004001215000300053Q0006360003000A000100010004163Q000A0001001215000300063Q00202Q000400030007001215000500083Q00202Q000500050009001215000600083Q00202Q00060006000A00062900073Q000100062Q00303Q00064Q00308Q00303Q00044Q00303Q00014Q00303Q00024Q00303Q00053Q00021F000800013Q0012090009000B4Q001D000A00073Q001209000B000C3Q001209000C000D4Q0013000A000C00022Q001D000B00084Q001D000C00094Q001D000D000A4Q0013000B000D0002001215000C000E4Q001D000D00073Q001209000E000F3Q001209000F00104Q0013000D000F00022Q001D000E000B4Q0031000C000E00012Q00333Q00013Q00023Q00023Q00026Q00F03F026Q00704002264Q002B00025Q001209000300014Q002A00045Q001209000500013Q0004240003002100012Q002F00076Q001D000800024Q002F000900014Q002F000A00024Q002F000B00034Q002F000C00044Q001D000D6Q001D000E00063Q002026000F000600012Q001E000C000F4Q003C000B3Q00022Q002F000C00034Q002F000D00044Q001D000E00014Q002A000F00014Q0035000F0006000F00101A000F0001000F2Q002A001000014Q003500100006001000101A0010000100100020260010001000012Q001E000D00104Q000C000C6Q003C000A3Q0002002034000A000A00022Q00280009000A4Q000D00073Q000100040B0003000500012Q002F000300054Q001D000400024Q0014000300044Q004300036Q00333Q00017Q00073Q00028Q00034Q00026Q00F03F03063Q00737472696E6703043Q006368617203043Q0062797465026Q00704002243Q001209000200014Q0011000300033Q00261C0002001F000100010004163Q001F0001001209000300023Q001209000400034Q002A00055Q001209000600033Q0004240004001E00012Q001D000800033Q001215000900043Q00202Q000900090005001215000A00043Q00202Q000A000A00062Q001D000B6Q001D000C00074Q0013000A000C0002001215000B00043Q00202Q000B000B00062Q001D000C00013Q002006000D000700032Q002A000E00014Q0035000D000D000E002026000D000D00032Q0013000B000D0002002034000B000B00072Q0002000A000A000B2Q003D0009000200022Q000E00030008000900040B000400090001001209000200033Q00261C00020002000100030004163Q000200012Q0005000300023Q0004163Q000200012Q00333Q00017Q00", GetFEnv(), ...);
