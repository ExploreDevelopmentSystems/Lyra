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
				if (Enum <= 38) then
					if (Enum <= 18) then
						if (Enum <= 8) then
							if (Enum <= 3) then
								if (Enum <= 1) then
									if (Enum > 0) then
										local A = Inst[2];
										Stk[A](Unpack(Stk, A + 1, Inst[3]));
									else
										do
											return Stk[Inst[2]];
										end
									end
								elseif (Enum == 2) then
									if (Stk[Inst[2]] == Inst[4]) then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								else
									local A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Top));
								end
							elseif (Enum <= 5) then
								if (Enum == 4) then
									do
										return;
									end
								else
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
								end
							elseif (Enum <= 6) then
								local A = Inst[2];
								do
									return Stk[A](Unpack(Stk, A + 1, Inst[3]));
								end
							elseif (Enum > 7) then
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							else
								local A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
							end
						elseif (Enum <= 13) then
							if (Enum <= 10) then
								if (Enum > 9) then
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
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
								end
							elseif (Enum <= 11) then
								local A = Inst[2];
								do
									return Unpack(Stk, A, Top);
								end
							elseif (Enum == 12) then
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
									if (Mvm[1] == 56) then
										Indexes[Idx - 1] = {Stk,Mvm[3]};
									else
										Indexes[Idx - 1] = {Upvalues,Mvm[3]};
									end
									Lupvals[#Lupvals + 1] = Indexes;
								end
								Stk[Inst[2]] = Wrap(NewProto, NewUvals, Env);
							else
								local A = Inst[2];
								local Results = {Stk[A](Stk[A + 1])};
								local Edx = 0;
								for Idx = A, Inst[4] do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
							end
						elseif (Enum <= 15) then
							if (Enum > 14) then
								local A = Inst[2];
								Stk[A](Stk[A + 1]);
							else
								for Idx = Inst[2], Inst[3] do
									Stk[Idx] = nil;
								end
							end
						elseif (Enum <= 16) then
							local A = Inst[2];
							local Results, Limit = _R(Stk[A](Stk[A + 1]));
							Top = (Limit + A) - 1;
							local Edx = 0;
							for Idx = A, Top do
								Edx = Edx + 1;
								Stk[Idx] = Results[Edx];
							end
						elseif (Enum > 17) then
							Stk[Inst[2]] = #Stk[Inst[3]];
						else
							local A = Inst[2];
							local Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
							Top = (Limit + A) - 1;
							local Edx = 0;
							for Idx = A, Top do
								Edx = Edx + 1;
								Stk[Idx] = Results[Edx];
							end
						end
					elseif (Enum <= 28) then
						if (Enum <= 23) then
							if (Enum <= 20) then
								if (Enum > 19) then
									Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
								else
									local A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Top));
								end
							elseif (Enum <= 21) then
								local B = Stk[Inst[4]];
								if not B then
									VIP = VIP + 1;
								else
									Stk[Inst[2]] = B;
									VIP = Inst[3];
								end
							elseif (Enum == 22) then
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
									if (Mvm[1] == 56) then
										Indexes[Idx - 1] = {Stk,Mvm[3]};
									else
										Indexes[Idx - 1] = {Upvalues,Mvm[3]};
									end
									Lupvals[#Lupvals + 1] = Indexes;
								end
								Stk[Inst[2]] = Wrap(NewProto, NewUvals, Env);
							else
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							end
						elseif (Enum <= 25) then
							if (Enum > 24) then
								local A = Inst[2];
								local Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Top)));
								Top = (Limit + A) - 1;
								local Edx = 0;
								for Idx = A, Top do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
							elseif (Stk[Inst[2]] == Inst[4]) then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						elseif (Enum <= 26) then
							Stk[Inst[2]] = Stk[Inst[3]] % Inst[4];
						elseif (Enum == 27) then
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
							Stk[A](Unpack(Stk, A + 1, Inst[3]));
						end
					elseif (Enum <= 33) then
						if (Enum <= 30) then
							if (Enum > 29) then
								VIP = Inst[3];
							else
								Stk[Inst[2]] = {};
							end
						elseif (Enum <= 31) then
							local A = Inst[2];
							Stk[A] = Stk[A](Stk[A + 1]);
						elseif (Enum == 32) then
							do
								return Stk[Inst[2]];
							end
						elseif not Stk[Inst[2]] then
							VIP = VIP + 1;
						else
							VIP = Inst[3];
						end
					elseif (Enum <= 35) then
						if (Enum > 34) then
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						else
							Stk[Inst[2]] = Inst[3] + Stk[Inst[4]];
						end
					elseif (Enum <= 36) then
						Stk[Inst[2]] = Upvalues[Inst[3]];
					elseif (Enum == 37) then
						Stk[Inst[2]] = Stk[Inst[3]];
					else
						VIP = Inst[3];
					end
				elseif (Enum <= 58) then
					if (Enum <= 48) then
						if (Enum <= 43) then
							if (Enum <= 40) then
								if (Enum == 39) then
									local A = Inst[2];
									Stk[A](Stk[A + 1]);
								else
									local A = Inst[2];
									do
										return Unpack(Stk, A, A + Inst[3]);
									end
								end
							elseif (Enum <= 41) then
								Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
							elseif (Enum > 42) then
								Stk[Inst[2]] = Stk[Inst[3]] % Stk[Inst[4]];
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
							if (Enum > 44) then
								local B = Inst[3];
								local K = Stk[B];
								for Idx = B + 1, Inst[4] do
									K = K .. Stk[Idx];
								end
								Stk[Inst[2]] = K;
							elseif Stk[Inst[2]] then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						elseif (Enum <= 46) then
							if Stk[Inst[2]] then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						elseif (Enum == 47) then
							local A = Inst[2];
							local B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
						else
							for Idx = Inst[2], Inst[3] do
								Stk[Idx] = nil;
							end
						end
					elseif (Enum <= 53) then
						if (Enum <= 50) then
							if (Enum == 49) then
								Stk[Inst[2]] = Inst[3];
							else
								do
									return;
								end
							end
						elseif (Enum <= 51) then
							local A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
						elseif (Enum > 52) then
							local A = Inst[2];
							do
								return Unpack(Stk, A, Top);
							end
						else
							local A = Inst[2];
							local Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
							Top = (Limit + A) - 1;
							local Edx = 0;
							for Idx = A, Top do
								Edx = Edx + 1;
								Stk[Idx] = Results[Edx];
							end
						end
					elseif (Enum <= 55) then
						if (Enum == 54) then
							Stk[Inst[2]] = #Stk[Inst[3]];
						else
							local B = Stk[Inst[4]];
							if not B then
								VIP = VIP + 1;
							else
								Stk[Inst[2]] = B;
								VIP = Inst[3];
							end
						end
					elseif (Enum <= 56) then
						Stk[Inst[2]] = Stk[Inst[3]];
					elseif (Enum > 57) then
						Stk[Inst[2]] = Stk[Inst[3]] % Inst[4];
					else
						Stk[Inst[2]] = {};
					end
				elseif (Enum <= 68) then
					if (Enum <= 63) then
						if (Enum <= 60) then
							if (Enum > 59) then
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							else
								local A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							end
						elseif (Enum <= 61) then
							Stk[Inst[2]] = Inst[3] + Stk[Inst[4]];
						elseif (Enum > 62) then
							Stk[Inst[2]] = Upvalues[Inst[3]];
						else
							local A = Inst[2];
							do
								return Stk[A](Unpack(Stk, A + 1, Inst[3]));
							end
						end
					elseif (Enum <= 65) then
						if (Enum > 64) then
							Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
						else
							local A = Inst[2];
							local Results = {Stk[A](Stk[A + 1])};
							local Edx = 0;
							for Idx = A, Inst[4] do
								Edx = Edx + 1;
								Stk[Idx] = Results[Edx];
							end
						end
					elseif (Enum <= 66) then
						Stk[Inst[2]] = Env[Inst[3]];
					elseif (Enum > 67) then
						Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
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
				elseif (Enum <= 73) then
					if (Enum <= 70) then
						if (Enum == 69) then
							Stk[Inst[2]] = Stk[Inst[3]] % Stk[Inst[4]];
						else
							Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
						end
					elseif (Enum <= 71) then
						local A = Inst[2];
						local B = Stk[Inst[3]];
						Stk[A + 1] = B;
						Stk[A] = B[Inst[4]];
					elseif (Enum > 72) then
						Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
					else
						Stk[Inst[2]] = Inst[3];
					end
				elseif (Enum <= 75) then
					if (Enum > 74) then
						if not Stk[Inst[2]] then
							VIP = VIP + 1;
						else
							VIP = Inst[3];
						end
					else
						Stk[Inst[2]] = Env[Inst[3]];
					end
				elseif (Enum <= 76) then
					local A = Inst[2];
					Stk[A] = Stk[A](Stk[A + 1]);
				elseif (Enum == 77) then
					local A = Inst[2];
					local Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Top)));
					Top = (Limit + A) - 1;
					local Edx = 0;
					for Idx = A, Top do
						Edx = Edx + 1;
						Stk[Idx] = Results[Edx];
					end
				else
					local B = Inst[3];
					local K = Stk[B];
					for Idx = B + 1, Inst[4] do
						K = K .. Stk[Idx];
					end
					Stk[Inst[2]] = K;
				end
				VIP = VIP + 1;
			end
		end;
	end
	return Wrap(Deserialize(), {}, vmenv)(...);
end
return VMCall("LOL!163Q0003063Q00737472696E6703043Q006368617203043Q00627974652Q033Q0073756203053Q0062697433322Q033Q0062697403043Q0062786F7203053Q007461626C6503063Q00636F6E63617403063Q00696E7365727403043Q0067616D65030A3Q0047657453657276696365030B3Q00D4546CF54E4324EA497BE003073Q00569C2018851D2603083Q008B9C51A94E6559A403073Q0037C7E523C81D1C030D3Q003BC9D920077DF4DB275D60E2C803053Q0073149ABC5403083Q006973666F6C646572030A3Q006D616B65666F6C64657203043Q005361766503043Q004C6F6164003C3Q0012423Q00013Q0020235Q0002001242000100013Q002023000100010003001242000200013Q002023000200020004001242000300053Q00064B0003000A000100010004263Q000A0001001242000300063Q002023000400030007001242000500083Q002023000500050009001242000600083Q00202300060006000A00060C00073Q000100062Q00383Q00064Q00388Q00383Q00044Q00383Q00014Q00383Q00024Q00383Q00053Q0012420008000B3Q00204700080008000C2Q0025000A00073Q001231000B000D3Q001231000C000E4Q0011000A000C4Q000900083Q00022Q001D00096Q0025000A00073Q001231000B000F3Q001231000C00104Q003B000A000C00022Q0025000B000A4Q0025000C00073Q001231000D00113Q001231000E00124Q003B000C000E00022Q002D000B000B000C001242000C00134Q0025000D000A4Q004C000C0002000200064B000C0030000100010004263Q00300001001242000C00144Q0025000D000A4Q000F000C0002000100060C000C0001000100032Q00383Q000B4Q00383Q00084Q00383Q00073Q00103C00090015000C00060C000C0002000100032Q00383Q000B4Q00383Q00084Q00383Q00073Q00103C00090016000C2Q0020000900024Q00043Q00013Q00033Q00023Q00026Q00F03F026Q00704002264Q001D00025Q001231000300014Q001200045Q001231000500013Q00040A0003002100012Q003F00076Q0025000800024Q003F000900014Q003F000A00024Q003F000B00034Q003F000C00044Q0025000D6Q0025000E00063Q002014000F000600012Q0011000C000F4Q0009000B3Q00022Q003F000C00034Q003F000D00044Q0025000E00014Q0012000F00014Q002B000F0006000F00103D000F0001000F2Q0012001000014Q002B00100006001000103D0010000100100020140010001000012Q0011000D00104Q004D000C6Q0009000A3Q000200203A000A000A00022Q002A0009000A4Q000300073Q000100041B0003000500012Q003F000300054Q0025000400024Q0006000300044Q000B00036Q00043Q00017Q000D3Q00028Q0003053Q007063612Q6C03043Q007761726E03283Q00EAF3943E808CC8D18E11C199D0D6812985FFC5D0CD3F80A9D49F9E2995ABD8D18A6CCCFFFADA947603063Q00DFB1BFED4CE103063Q0073DBB235426A03073Q00DB36A9C05A305003083Q00746F737472696E6703053Q007072696E74032C3Q00726E19374871192B4A7F40165C4103205A510630454E19655A4316204D0213205D56092B4E024D656247197F03043Q004529226003063Q008AC2DB1F077103063Q004BDCA3B76A62032D3Q001231000300014Q000E000400053Q00261800030002000100010004263Q00020001001242000600023Q00060C00073Q000100042Q00248Q00243Q00014Q00383Q00014Q00383Q00024Q00400006000200072Q0025000500074Q0025000400063Q00064B0004001E000100010004263Q001E0001001242000600034Q003F000700023Q001231000800043Q001231000900054Q003B0007000900022Q0025000800014Q003F000900023Q001231000A00063Q001231000B00074Q003B0009000B0002001242000A00084Q0025000B00054Q002A000A000B4Q000300063Q00010004263Q002C0001001242000600094Q003F000700023Q0012310008000A3Q0012310009000B4Q003B0007000900022Q0025000800014Q003F000900023Q001231000A000C3Q001231000B000D4Q003B0009000B00022Q0025000A00024Q00010006000A00010004263Q002C00010004263Q000200012Q00043Q00013Q00013Q00073Q00028Q00026Q00F03F03093Q00777269746566696C65030A3Q004A534F4E456E636F646503063Q00697366696C65030A3Q004A534F4E4465636F646503083Q007265616466696C6500233Q0012313Q00014Q000E000100013Q0026183Q000C000100020004263Q000C0001001242000200034Q003F00036Q003F000400013Q0020470004000400042Q0025000600014Q0011000400064Q000300023Q00010004263Q002200010026183Q0002000100010004263Q00020001001242000200054Q003F00036Q004C00020002000200062C0002001B00013Q0004263Q001B00012Q003F000200013Q002047000200020006001242000400074Q003F00056Q002A000400054Q000900023Q00020006150001001D000100020004263Q001D00012Q001D00026Q0025000100024Q003F000200024Q003F000300034Q00460001000200030012313Q00023Q0004263Q000200012Q00043Q00017Q000D3Q00028Q0003053Q007063612Q6C03053Q007072696E74032D3Q0039969225D831A38534E442899E34DA07A99831CC0EB69277D50DBB8F32DD42A98E23CD0BB48C779442918E2E8303053Q00B962DAEB5703063Q00FD3D2BF3DBF003063Q00CAAB5C4786BE03043Q007761726E03283Q0012ED359A28F235862AFC6CAE28C8208D2D81388769CD23892D813F8D3DD525862E8161C802C435D203043Q00E849A14C03063Q009ECB50520CE103053Q007EDBB9223D03083Q00746F737472696E6703373Q001231000300014Q000E000400053Q00261800030002000100010004263Q00020001001242000600023Q00060C00073Q000100042Q00248Q00243Q00014Q00383Q00014Q00383Q00024Q00400006000200072Q0025000500074Q0025000400063Q00062C0004002100013Q0004263Q00210001001231000600013Q00261800060010000100010004263Q00100001001242000700034Q003F000800023Q001231000900043Q001231000A00054Q003B0008000A00022Q0025000900014Q003F000A00023Q001231000B00063Q001231000C00074Q003B000A000C00022Q0025000B00054Q00010007000B00012Q0020000500023Q0004263Q001000010004263Q00360001001231000600013Q00261800060022000100010004263Q00220001001242000700084Q003F000800023Q001231000900093Q001231000A000A4Q003B0008000A00022Q0025000900014Q003F000A00023Q001231000B000B3Q001231000C000C4Q003B000A000C0002001242000B000D4Q0025000C00054Q002A000B000C4Q000300073Q00012Q0020000200023Q0004263Q002200010004263Q003600010004263Q000200012Q00043Q00013Q00013Q00043Q00028Q0003063Q00697366696C65030A3Q004A534F4E4465636F646503083Q007265616466696C65001B3Q0012313Q00014Q000E000100013Q0026183Q0002000100010004263Q00020001001242000200024Q003F00036Q004C00020002000200062C0002001100013Q0004263Q001100012Q003F000200013Q002047000200020003001242000400044Q003F00056Q002A000400054Q000900023Q000200061500010013000100020004263Q001300012Q001D00026Q0025000100024Q003F000200024Q002900020001000200064B00020018000100010004263Q001800012Q003F000200034Q0020000200023Q0004263Q000200012Q00043Q00017Q00", GetFEnv(), ...);
