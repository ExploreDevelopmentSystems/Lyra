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
				if (Enum <= 36) then
					if (Enum <= 17) then
						if (Enum <= 8) then
							if (Enum <= 3) then
								if (Enum <= 1) then
									if (Enum == 0) then
										if Stk[Inst[2]] then
											VIP = VIP + 1;
										else
											VIP = Inst[3];
										end
									else
										VIP = Inst[3];
									end
								elseif (Enum == 2) then
									do
										return;
									end
								else
									local A = Inst[2];
									do
										return Unpack(Stk, A, Top);
									end
								end
							elseif (Enum <= 5) then
								if (Enum > 4) then
									local A = Inst[2];
									do
										return Unpack(Stk, A, A + Inst[3]);
									end
								else
									Stk[Inst[2]] = Inst[3];
								end
							elseif (Enum <= 6) then
								Stk[Inst[2]] = Stk[Inst[3]];
							elseif (Enum == 7) then
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
									if (Mvm[1] == 16) then
										Indexes[Idx - 1] = {Stk,Mvm[3]};
									else
										Indexes[Idx - 1] = {Upvalues,Mvm[3]};
									end
									Lupvals[#Lupvals + 1] = Indexes;
								end
								Stk[Inst[2]] = Wrap(NewProto, NewUvals, Env);
							else
								local A = Inst[2];
								local C = Inst[4];
								local CB = A + 2;
								local Result = {Stk[A](Stk[A + 1], Stk[CB])};
								for Idx = 1, C do
									Stk[CB + Idx] = Result[Idx];
								end
								local R = Result[1];
								if R then
									Stk[CB] = R;
									VIP = Inst[3];
								else
									VIP = VIP + 1;
								end
							end
						elseif (Enum <= 12) then
							if (Enum <= 10) then
								if (Enum > 9) then
									if not Stk[Inst[2]] then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								else
									local A = Inst[2];
									local Results = {Stk[A](Stk[A + 1])};
									local Edx = 0;
									for Idx = A, Inst[4] do
										Edx = Edx + 1;
										Stk[Idx] = Results[Edx];
									end
								end
							elseif (Enum > 11) then
								do
									return;
								end
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
							if (Enum == 13) then
								Stk[Inst[2]] = Upvalues[Inst[3]];
							elseif (Stk[Inst[2]] == Inst[4]) then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						elseif (Enum <= 15) then
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
						elseif (Enum > 16) then
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						else
							Stk[Inst[2]] = Stk[Inst[3]];
						end
					elseif (Enum <= 26) then
						if (Enum <= 21) then
							if (Enum <= 19) then
								if (Enum > 18) then
									local A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								else
									Stk[Inst[2]] = Stk[Inst[3]] % Inst[4];
								end
							elseif (Enum == 20) then
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
									if (Mvm[1] == 16) then
										Indexes[Idx - 1] = {Stk,Mvm[3]};
									else
										Indexes[Idx - 1] = {Upvalues,Mvm[3]};
									end
									Lupvals[#Lupvals + 1] = Indexes;
								end
								Stk[Inst[2]] = Wrap(NewProto, NewUvals, Env);
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
						elseif (Enum <= 23) then
							if (Enum == 22) then
								Stk[Inst[2]] = Stk[Inst[3]] % Stk[Inst[4]];
							else
								local A = Inst[2];
								do
									return Stk[A](Unpack(Stk, A + 1, Inst[3]));
								end
							end
						elseif (Enum <= 24) then
							local A = Inst[2];
							local C = Inst[4];
							local CB = A + 2;
							local Result = {Stk[A](Stk[A + 1], Stk[CB])};
							for Idx = 1, C do
								Stk[CB + Idx] = Result[Idx];
							end
							local R = Result[1];
							if R then
								Stk[CB] = R;
								VIP = Inst[3];
							else
								VIP = VIP + 1;
							end
						elseif (Enum > 25) then
							local A = Inst[2];
							Stk[A](Unpack(Stk, A + 1, Top));
						elseif (Stk[Inst[2]] == Stk[Inst[4]]) then
							VIP = VIP + 1;
						else
							VIP = Inst[3];
						end
					elseif (Enum <= 31) then
						if (Enum <= 28) then
							if (Enum > 27) then
								Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
							else
								local A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							end
						elseif (Enum <= 29) then
							for Idx = Inst[2], Inst[3] do
								Stk[Idx] = nil;
							end
						elseif (Enum > 30) then
							local A = Inst[2];
							local Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
							Top = (Limit + A) - 1;
							local Edx = 0;
							for Idx = A, Top do
								Edx = Edx + 1;
								Stk[Idx] = Results[Edx];
							end
						else
							local A = Inst[2];
							local B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
						end
					elseif (Enum <= 33) then
						if (Enum > 32) then
							local A = Inst[2];
							Stk[A](Unpack(Stk, A + 1, Top));
						else
							Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
						end
					elseif (Enum <= 34) then
						local A = Inst[2];
						Stk[A] = Stk[A](Stk[A + 1]);
					elseif (Enum == 35) then
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
						local B = Stk[Inst[3]];
						Stk[A + 1] = B;
						Stk[A] = B[Inst[4]];
					end
				elseif (Enum <= 54) then
					if (Enum <= 45) then
						if (Enum <= 40) then
							if (Enum <= 38) then
								if (Enum > 37) then
									Stk[Inst[2]] = Env[Inst[3]];
								else
									Stk[Inst[2]] = Inst[3];
								end
							elseif (Enum > 39) then
								Stk[Inst[2]] = {};
							else
								local A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
							end
						elseif (Enum <= 42) then
							if (Enum == 41) then
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
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
						elseif (Enum <= 43) then
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
						elseif (Enum > 44) then
							local A = Inst[2];
							local Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
							Top = (Limit + A) - 1;
							local Edx = 0;
							for Idx = A, Top do
								Edx = Edx + 1;
								Stk[Idx] = Results[Edx];
							end
						else
							Stk[Inst[2]] = Upvalues[Inst[3]];
						end
					elseif (Enum <= 49) then
						if (Enum <= 47) then
							if (Enum == 46) then
								Stk[Inst[2]] = Inst[3] + Stk[Inst[4]];
							elseif (Stk[Inst[2]] == Stk[Inst[4]]) then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						elseif (Enum > 48) then
							Stk[Inst[2]] = Env[Inst[3]];
						else
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						end
					elseif (Enum <= 51) then
						if (Enum == 50) then
							local A = Inst[2];
							local Results, Limit = _R(Stk[A](Stk[A + 1]));
							Top = (Limit + A) - 1;
							local Edx = 0;
							for Idx = A, Top do
								Edx = Edx + 1;
								Stk[Idx] = Results[Edx];
							end
						else
							Stk[Inst[2]] = Stk[Inst[3]] % Inst[4];
						end
					elseif (Enum <= 52) then
						do
							return Stk[Inst[2]];
						end
					elseif (Enum == 53) then
						Stk[Inst[2]] = #Stk[Inst[3]];
					else
						do
							return Stk[Inst[2]]();
						end
					end
				elseif (Enum <= 63) then
					if (Enum <= 58) then
						if (Enum <= 56) then
							if (Enum > 55) then
								local A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
							else
								local A = Inst[2];
								do
									return Unpack(Stk, A, A + Inst[3]);
								end
							end
						elseif (Enum > 57) then
							Stk[Inst[2]] = {};
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
					elseif (Enum <= 60) then
						if (Enum > 59) then
							VIP = Inst[3];
						else
							Stk[Inst[2]] = Stk[Inst[3]] % Stk[Inst[4]];
						end
					elseif (Enum <= 61) then
						local A = Inst[2];
						do
							return Unpack(Stk, A, Top);
						end
					elseif (Enum > 62) then
						Stk[Inst[2]] = Inst[3] + Stk[Inst[4]];
					elseif (Stk[Inst[2]] == Inst[4]) then
						VIP = VIP + 1;
					else
						VIP = Inst[3];
					end
				elseif (Enum <= 68) then
					if (Enum <= 65) then
						if (Enum > 64) then
							do
								return Stk[Inst[2]]();
							end
						else
							local A = Inst[2];
							do
								return Stk[A](Unpack(Stk, A + 1, Inst[3]));
							end
						end
					elseif (Enum <= 66) then
						for Idx = Inst[2], Inst[3] do
							Stk[Idx] = nil;
						end
					elseif (Enum > 67) then
						local A = Inst[2];
						local Results, Limit = _R(Stk[A](Stk[A + 1]));
						Top = (Limit + A) - 1;
						local Edx = 0;
						for Idx = A, Top do
							Edx = Edx + 1;
							Stk[Idx] = Results[Edx];
						end
					else
						local A = Inst[2];
						Stk[A] = Stk[A](Stk[A + 1]);
					end
				elseif (Enum <= 70) then
					if (Enum == 69) then
						local A = Inst[2];
						local Results = {Stk[A](Stk[A + 1])};
						local Edx = 0;
						for Idx = A, Inst[4] do
							Edx = Edx + 1;
							Stk[Idx] = Results[Edx];
						end
					elseif Stk[Inst[2]] then
						VIP = VIP + 1;
					else
						VIP = Inst[3];
					end
				elseif (Enum <= 71) then
					Stk[Inst[2]] = #Stk[Inst[3]];
				elseif (Enum == 72) then
					do
						return Stk[Inst[2]];
					end
				elseif not Stk[Inst[2]] then
					VIP = VIP + 1;
				else
					VIP = Inst[3];
				end
				VIP = VIP + 1;
			end
		end;
	end
	return Wrap(Deserialize(), {}, vmenv)(...);
end
return VMCall("LOL!0E3Q0003063Q00737472696E6703043Q006368617203043Q00627974652Q033Q0073756203053Q0062697433322Q033Q0062697403043Q0062786F7203053Q007461626C6503063Q00636F6E63617403063Q00696E7365727403753Q00F3BF3000258CB4E436112198FCA2301823D4EEB8210235D9F5BF211E2298F8A4295F13CEEBA72B0233F2FEBD211C39C6F6AE2A0405CFE8BF211D2599D7B2361179C4FEAD375F3ED3FAAF375F3BD7F2A56B3A31FCCE861C2A06F7EBE40F1E6FC5F4AC214013FBB4A5720517C7E2A4723A0E98F7BE2503063Q00B69BCB447056030D3Q00466574636847616D6544617461030E3Q0044657465637447616D655479706500243Q0012263Q00013Q0020305Q0002001226000100013Q002030000100010003001226000200013Q002030000200020004001226000300053Q00060A0003000A000100010004013Q000A0001001226000300063Q002030000400030007001226000500083Q002030000500050009001226000600083Q00203000060006000A00060700073Q000100062Q00103Q00064Q00108Q00103Q00044Q00103Q00014Q00103Q00024Q00103Q00054Q0006000800073Q0012250009000B3Q001225000A000C4Q00130008000A00022Q003A00095Q000607000A0001000100022Q00103Q00084Q00103Q00073Q00102B0009000D000A000607000A0002000100012Q00103Q00073Q00102B0009000E000A2Q0034000900024Q000C3Q00013Q00033Q00023Q00026Q00F03F026Q00704002264Q003A00025Q001225000300014Q004700045Q001225000500013Q00040F0003002100012Q000D00076Q0006000800024Q000D000900014Q000D000A00024Q000D000B00034Q000D000C00044Q0006000D6Q0006000E00063Q002Q20000F000600012Q002D000C000F4Q0027000B3Q00022Q000D000C00034Q000D000D00044Q0006000E00014Q0047000F00014Q003B000F0006000F00102E000F0001000F2Q0047001000014Q003B00100006001000102E001000010010002Q200010001000012Q002D000D00104Q000B000C6Q0027000A3Q0002002033000A000A00022Q00320009000A4Q001A00073Q00010004390003000500012Q000D000300054Q0006000400024Q0040000300044Q003D00036Q000C3Q00017Q00063Q00028Q0003053Q007063612Q6C03043Q007761726E03293Q0085DF47A8BBDC43B1BBFB52AAACC50683BFF14AA0BAB852AA2QFE43B1BDF006A2BFF543E5BAF952A4E403043Q00C5DE982603083Q00746F737472696E6701203Q001225000100014Q001D000200033Q00263E00010002000100010004013Q00020001001226000400023Q00060700053Q000100012Q002C8Q00090004000200052Q0006000300054Q0006000200043Q0006460002000E00013Q0004013Q000E00012Q0034000300023Q0004013Q001F0001001225000400013Q00263E0004000F000100010004013Q000F0001001226000500034Q000D000600013Q001225000700043Q001225000800054Q0013000600080002001226000700064Q0006000800034Q0032000700084Q001A00053Q00012Q001D000500054Q0034000500023Q0004013Q000F00010004013Q001F00010004013Q000200012Q000C3Q00013Q00013Q00033Q00030A3Q006C6F6164737472696E6703043Q0067616D6503073Q00482Q747047657400093Q0012263Q00013Q001226000100023Q00201E0001000100032Q000D00036Q002D000100034Q00275Q00022Q00363Q00014Q003D8Q000C3Q00017Q00143Q00028Q00026Q00F03F03063Q00697061697273030C3Q005072656D69756D47616D657303023Q00496403073Q00CC527DE874533B03073Q00569C2018851D2603043Q004E616D65030A3Q004578656375746555726C03323Q00938D4ABB3D7544E78403B86F795AAE904EE87A7D5AA2CB0389733C56A4914ABE783C5CA29C03A16E3C45A29456A16F7953E903073Q0037C7E523C81D1C03093Q0046722Q6547616D657303043Q0052E8D93103053Q0073149ABC54027Q004003073Q00E4D186228EA8DF03063Q00DFB1BFED4CE1030D3Q00466574636847616D6544617461031A3Q0070C8A9365534FB42C6E03C5524B85E89A73B5D35FB52C8B43B1E03073Q00DB36A9C05A3050034C3Q001225000300014Q001D000400043Q00263E00030034000100020004013Q00340001001226000500033Q00203000060004000400060A00060009000100010004013Q000900012Q003A00066Q00090005000200070004013Q001E0001002030000A00090005000619000A001E000100010004013Q001E00010006460002001800013Q0004013Q001800012Q000D000A5Q001225000B00063Q001225000C00074Q0013000A000C0002002030000B00090008002030000C000900092Q0005000A00023Q0004013Q001E00012Q001D000A000A4Q000D000B5Q001225000C000A3Q001225000D000B4Q002D000B000D4Q003D000A5Q0006080005000B000100020004013Q000B0001001226000500033Q00203000060004000C00060A00060025000100010004013Q002500012Q003A00066Q00090005000200070004013Q00310001002030000A00090005000619000A0031000100010004013Q003100012Q000D000A5Q001225000B000D3Q001225000C000E4Q0013000A000C0002002030000B00090008002030000C000900092Q0005000A00023Q00060800050027000100020004013Q002700010012250003000F3Q00263E0003003C0001000F0004013Q003C00012Q000D00055Q001225000600103Q001225000700114Q00130005000700022Q001D000600074Q0005000500023Q00263E00030002000100010004013Q0002000100201E00053Q00122Q00430005000200022Q0006000400053Q00060A00040049000100010004013Q004900012Q001D000500054Q000D00065Q001225000700133Q001225000800144Q002D000600084Q003D00055Q001225000300023Q0004013Q000200012Q000C3Q00017Q00", GetFEnv(), ...);
