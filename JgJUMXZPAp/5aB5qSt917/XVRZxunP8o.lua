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
									if (Enum == 0) then
										local A = Inst[2];
										local Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Top)));
										Top = (Limit + A) - 1;
										local Edx = 0;
										for Idx = A, Top do
											Edx = Edx + 1;
											Stk[Idx] = Results[Edx];
										end
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
											if (Mvm[1] == 76) then
												Indexes[Idx - 1] = {Stk,Mvm[3]};
											else
												Indexes[Idx - 1] = {Upvalues,Mvm[3]};
											end
											Lupvals[#Lupvals + 1] = Indexes;
										end
										Stk[Inst[2]] = Wrap(NewProto, NewUvals, Env);
									end
								elseif (Enum == 2) then
									local A = Inst[2];
									Stk[A] = Stk[A](Stk[A + 1]);
								else
									Stk[Inst[2]] = Stk[Inst[3]];
								end
							elseif (Enum <= 5) then
								if (Enum == 4) then
									Stk[Inst[2]] = Inst[3];
								else
									do
										return Stk[Inst[2]]();
									end
								end
							elseif (Enum <= 6) then
								Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
							elseif (Enum > 7) then
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
							else
								local A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
							end
						elseif (Enum <= 13) then
							if (Enum <= 10) then
								if (Enum > 9) then
									if (Inst[2] == Stk[Inst[4]]) then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
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
							elseif (Enum <= 11) then
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							elseif (Enum > 12) then
								VIP = Inst[3];
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
						elseif (Enum <= 15) then
							if (Enum > 14) then
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
						elseif (Enum <= 16) then
							do
								return Stk[Inst[2]];
							end
						elseif (Enum > 17) then
							local A = Inst[2];
							Stk[A] = Stk[A](Stk[A + 1]);
						else
							Stk[Inst[2]] = Stk[Inst[3]] % Stk[Inst[4]];
						end
					elseif (Enum <= 28) then
						if (Enum <= 23) then
							if (Enum <= 20) then
								if (Enum > 19) then
									if (Stk[Inst[2]] == Stk[Inst[4]]) then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								else
									local A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Top));
								end
							elseif (Enum <= 21) then
								local A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Top));
							elseif (Enum == 22) then
								if not Stk[Inst[2]] then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
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
						elseif (Enum <= 25) then
							if (Enum == 24) then
								if (Stk[Inst[2]] == Inst[4]) then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							else
								Stk[Inst[2]] = Stk[Inst[3]] % Inst[4];
							end
						elseif (Enum <= 26) then
							local A = Inst[2];
							local Results = {Stk[A](Stk[A + 1])};
							local Edx = 0;
							for Idx = A, Inst[4] do
								Edx = Edx + 1;
								Stk[Idx] = Results[Edx];
							end
						elseif (Enum > 27) then
							local A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
						elseif Stk[Inst[2]] then
							VIP = VIP + 1;
						else
							VIP = Inst[3];
						end
					elseif (Enum <= 33) then
						if (Enum <= 30) then
							if (Enum == 29) then
								Stk[Inst[2]] = Env[Inst[3]];
							else
								Stk[Inst[2]] = Inst[3];
							end
						elseif (Enum <= 31) then
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
						elseif (Enum > 32) then
							if (Stk[Inst[2]] == Stk[Inst[4]]) then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						else
							local A = Inst[2];
							do
								return Unpack(Stk, A, A + Inst[3]);
							end
						end
					elseif (Enum <= 35) then
						if (Enum > 34) then
							Stk[Inst[2]] = Stk[Inst[3]] % Stk[Inst[4]];
						else
							local A = Inst[2];
							do
								return Unpack(Stk, A, Top);
							end
						end
					elseif (Enum <= 36) then
						VIP = Inst[3];
					elseif (Enum > 37) then
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
							if (Mvm[1] == 76) then
								Indexes[Idx - 1] = {Stk,Mvm[3]};
							else
								Indexes[Idx - 1] = {Upvalues,Mvm[3]};
							end
							Lupvals[#Lupvals + 1] = Indexes;
						end
						Stk[Inst[2]] = Wrap(NewProto, NewUvals, Env);
					else
						local A = Inst[2];
						Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
					end
				elseif (Enum <= 57) then
					if (Enum <= 47) then
						if (Enum <= 42) then
							if (Enum <= 40) then
								if (Enum == 39) then
									local A = Inst[2];
									do
										return Stk[A](Unpack(Stk, A + 1, Inst[3]));
									end
								else
									local B = Stk[Inst[4]];
									if not B then
										VIP = VIP + 1;
									else
										Stk[Inst[2]] = B;
										VIP = Inst[3];
									end
								end
							elseif (Enum == 41) then
								Stk[Inst[2]] = #Stk[Inst[3]];
							else
								do
									return;
								end
							end
						elseif (Enum <= 44) then
							if (Enum == 43) then
								Stk[Inst[2]] = Env[Inst[3]];
							else
								Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
							end
						elseif (Enum <= 45) then
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
						elseif (Enum > 46) then
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
						else
							Stk[Inst[2]] = {};
						end
					elseif (Enum <= 52) then
						if (Enum <= 49) then
							if (Enum == 48) then
								if not Stk[Inst[2]] then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							else
								Stk[Inst[2]] = Inst[3] + Stk[Inst[4]];
							end
						elseif (Enum <= 50) then
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						elseif (Enum > 51) then
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
							local Results, Limit = _R(Stk[A](Stk[A + 1]));
							Top = (Limit + A) - 1;
							local Edx = 0;
							for Idx = A, Top do
								Edx = Edx + 1;
								Stk[Idx] = Results[Edx];
							end
						end
					elseif (Enum <= 54) then
						if (Enum > 53) then
							do
								return Stk[Inst[2]];
							end
						else
							Stk[Inst[2]] = {};
						end
					elseif (Enum <= 55) then
						local A = Inst[2];
						local B = Stk[Inst[3]];
						Stk[A + 1] = B;
						Stk[A] = B[Inst[4]];
					elseif (Enum == 56) then
						if Stk[Inst[2]] then
							VIP = VIP + 1;
						else
							VIP = Inst[3];
						end
					elseif (Stk[Inst[2]] == Inst[4]) then
						VIP = VIP + 1;
					else
						VIP = Inst[3];
					end
				elseif (Enum <= 67) then
					if (Enum <= 62) then
						if (Enum <= 59) then
							if (Enum == 58) then
								local A = Inst[2];
								local B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
							else
								Stk[Inst[2]] = Stk[Inst[3]] % Inst[4];
							end
						elseif (Enum <= 60) then
							local A = Inst[2];
							do
								return Unpack(Stk, A, A + Inst[3]);
							end
						elseif (Enum == 61) then
							local B = Stk[Inst[4]];
							if not B then
								VIP = VIP + 1;
							else
								Stk[Inst[2]] = B;
								VIP = Inst[3];
							end
						else
							for Idx = Inst[2], Inst[3] do
								Stk[Idx] = nil;
							end
						end
					elseif (Enum <= 64) then
						if (Enum > 63) then
							Stk[Inst[2]] = Inst[3] + Stk[Inst[4]];
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
					elseif (Enum <= 65) then
						Stk[Inst[2]] = Upvalues[Inst[3]];
					elseif (Enum > 66) then
						if (Inst[2] == Stk[Inst[4]]) then
							VIP = VIP + 1;
						else
							VIP = Inst[3];
						end
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
				elseif (Enum <= 72) then
					if (Enum <= 69) then
						if (Enum > 68) then
							local A = Inst[2];
							do
								return Unpack(Stk, A, Top);
							end
						else
							for Idx = Inst[2], Inst[3] do
								Stk[Idx] = nil;
							end
						end
					elseif (Enum <= 70) then
						local A = Inst[2];
						local Results, Limit = _R(Stk[A](Stk[A + 1]));
						Top = (Limit + A) - 1;
						local Edx = 0;
						for Idx = A, Top do
							Edx = Edx + 1;
							Stk[Idx] = Results[Edx];
						end
					elseif (Enum == 71) then
						do
							return Stk[Inst[2]]();
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
				elseif (Enum <= 74) then
					if (Enum > 73) then
						Stk[Inst[2]] = #Stk[Inst[3]];
					else
						do
							return;
						end
					end
				elseif (Enum <= 75) then
					Stk[Inst[2]] = Upvalues[Inst[3]];
				elseif (Enum == 76) then
					Stk[Inst[2]] = Stk[Inst[3]];
				else
					local A = Inst[2];
					Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
				end
				VIP = VIP + 1;
			end
		end;
	end
	return Wrap(Deserialize(), {}, vmenv)(...);
end
return VMCall("LOL!0E3Q0003063Q00737472696E6703043Q006368617203043Q00627974652Q033Q0073756203053Q0062697433322Q033Q0062697403043Q0062786F7203053Q007461626C6503063Q00636F6E63617403063Q00696E7365727403753Q001E3606C6E8F11F593013C1B5AC59022A07D4EEB85504211DD8EFAE5E026C11D9F6E4750E321ED9E9AE74133417DAF4BB5D132C06E5E2B844132F0199D7B242176D00D3FDB81F1E2713D2E8E45D172B1C99D1AC7A230F2AECCB8A4059091C8FE8A457137237FBB4A5063Q03CFF4FD7A2E6C1EC3FA03073Q0030764272B69BCB030D3Q00466574636847616D6544617461030E3Q0044657465637447616D655479706500233Q00122B3Q00013Q00200B5Q000200122B000100013Q00200B00010001000300122B000200013Q00200B00020002000400122B000300053Q0006160003000A000100010004243Q000A000100122B000300063Q00200B00040003000700122B000500083Q00200B00050005000900122B000600083Q00200B00060006000A00060100073Q000100062Q004C3Q00064Q004C8Q004C3Q00044Q004C3Q00014Q004C3Q00024Q004C3Q00054Q0003000800073Q0012040009000B3Q001204000A000C4Q004D0008000A00022Q003500095Q000601000A0001000100012Q004C3Q00083Q00101F0009000D000A000601000A0002000100012Q004C3Q00073Q00101F0009000E000A2Q0036000900024Q00493Q00013Q00033Q00023Q00026Q00F03F026Q00704002264Q003500025Q001204000300014Q002900045Q001204000500013Q00042D0003002100012Q004100076Q0003000800024Q0041000900014Q0041000A00024Q0041000B00034Q0041000C00044Q0003000D6Q0003000E00063Q00202C000F000600012Q000C000C000F4Q0025000B3Q00022Q0041000C00034Q0041000D00044Q0003000E00014Q0029000F00014Q0011000F0006000F001040000F0001000F2Q0029001000014Q001100100006001000104000100001001000202C0010001000012Q000C000D00104Q0017000C6Q0025000A3Q000200203B000A000A00022Q00460009000A4Q001300073Q00010004090003000500012Q0041000300054Q0003000400024Q0027000300044Q004500036Q00493Q00017Q00023Q00028Q0003053Q007063612Q6C01123Q001204000100014Q003E000200033Q00261800010002000100010004243Q0002000100122B000400023Q00060100053Q000100012Q004B8Q00480004000200052Q0003000300054Q0003000200043Q0006380002000E00013Q0004243Q000E000100063D0004000F000100030004243Q000F00012Q003E000400044Q0036000400023Q0004243Q000200012Q00493Q00013Q00013Q00033Q00030A3Q006C6F6164737472696E6703043Q0067616D6503073Q00482Q747047657400093Q00122B3Q00013Q00122B000100023Q0020370001000100032Q004100036Q000C000100034Q00255Q00022Q00473Q00014Q00458Q00493Q00017Q00143Q00028Q00026Q00F03F03053Q007061697273030C3Q005072656D69756D47616D657303023Q00496403073Q000661A0B319237E03053Q00705613C5DE03043Q004E616D65030A3Q004578656375746555726C03243Q00ED24F94D71F04B9D31FD4D7DA554D827E9496AE0559D37F20079E652D420F90073E05F9303073Q0026BD569C20188503093Q0046722Q6547616D657303043Q00DA45A24303043Q00269C37C7027Q0040030D3Q00466574636847616D6544617461031A3Q008E7C75241670BA57A73D7A2D0777F203AF7C712D5370FB57A93303083Q0023C81D1C4873149A03073Q002CB1DAD1823B3A03073Q005479DFB1BFED4C034C3Q001204000300014Q003E000400043Q000E4300020034000100030004243Q0034000100122B000500033Q00200B00060004000400061600060009000100010004243Q000900012Q003500066Q00480005000200070004243Q001E000100200B000A00090005000621000A001E000100010004243Q001E00010006380002001800013Q0004243Q001800012Q0041000A5Q001204000B00063Q001204000C00074Q004D000A000C000200200B000B0009000800200B000C000900092Q0020000A00023Q0004243Q001E00012Q003E000A000A4Q0041000B5Q001204000C000A3Q001204000D000B4Q000C000B000D4Q0045000A5Q0006420005000B000100020004243Q000B000100122B000500033Q00200B00060004000C00061600060025000100010004243Q002500012Q003500066Q00480005000200070004243Q0031000100200B000A00090005000621000A0031000100010004243Q003100012Q0041000A5Q001204000B000D3Q001204000C000E4Q004D000A000C000200200B000B0009000800200B000C000900092Q0020000A00023Q00064200050027000100020004243Q002700010012040003000F3Q00261800030042000100010004243Q0042000100203700053Q00102Q00120005000200022Q0003000400053Q00061600040041000100010004243Q004100012Q003E000500054Q004100065Q001204000700113Q001204000800124Q000C000600084Q004500055Q001204000300023Q002618000300020001000F0004243Q000200012Q004100055Q001204000600133Q001204000700144Q004D0005000700022Q003E000600074Q0020000500023Q0004243Q000200012Q00493Q00017Q00", GetFEnv(), ...);
