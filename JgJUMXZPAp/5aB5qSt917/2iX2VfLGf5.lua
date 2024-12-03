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
										Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									else
										local A = Inst[2];
										Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
									end
								elseif (Enum > 2) then
									do
										return;
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
							elseif (Enum <= 5) then
								if (Enum == 4) then
									Stk[Inst[2]] = Stk[Inst[3]] % Stk[Inst[4]];
								else
									local A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
								end
							elseif (Enum <= 6) then
								Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
							elseif (Enum > 7) then
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
									if (Mvm[1] == 65) then
										Indexes[Idx - 1] = {Stk,Mvm[3]};
									else
										Indexes[Idx - 1] = {Upvalues,Mvm[3]};
									end
									Lupvals[#Lupvals + 1] = Indexes;
								end
								Stk[Inst[2]] = Wrap(NewProto, NewUvals, Env);
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
						elseif (Enum <= 13) then
							if (Enum <= 10) then
								if (Enum > 9) then
									local A = Inst[2];
									do
										return Stk[A](Unpack(Stk, A + 1, Inst[3]));
									end
								else
									Stk[Inst[2]] = {};
								end
							elseif (Enum <= 11) then
								local A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
							elseif (Enum > 12) then
								Stk[Inst[2]] = Inst[3] + Stk[Inst[4]];
							else
								local A = Inst[2];
								do
									return Unpack(Stk, A, A + Inst[3]);
								end
							end
						elseif (Enum <= 15) then
							if (Enum == 14) then
								local B = Inst[3];
								local K = Stk[B];
								for Idx = B + 1, Inst[4] do
									K = K .. Stk[Idx];
								end
								Stk[Inst[2]] = K;
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
						elseif (Enum <= 16) then
							Stk[Inst[2]] = Stk[Inst[3]] % Inst[4];
						elseif (Enum == 17) then
							local A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
						else
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
						end
					elseif (Enum <= 28) then
						if (Enum <= 23) then
							if (Enum <= 20) then
								if (Enum == 19) then
									do
										return;
									end
								else
									local A = Inst[2];
									local B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
								end
							elseif (Enum <= 21) then
								local A = Inst[2];
								local Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Top)));
								Top = (Limit + A) - 1;
								local Edx = 0;
								for Idx = A, Top do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
							elseif (Enum == 22) then
								local B = Stk[Inst[4]];
								if not B then
									VIP = VIP + 1;
								else
									Stk[Inst[2]] = B;
									VIP = Inst[3];
								end
							else
								do
									return Stk[Inst[2]];
								end
							end
						elseif (Enum <= 25) then
							if (Enum > 24) then
								local A = Inst[2];
								Stk[A](Stk[A + 1]);
							elseif not Stk[Inst[2]] then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						elseif (Enum <= 26) then
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
						elseif (Enum > 27) then
							Stk[Inst[2]] = Env[Inst[3]];
						else
							Stk[Inst[2]] = Upvalues[Inst[3]];
						end
					elseif (Enum <= 33) then
						if (Enum <= 30) then
							if (Enum == 29) then
								local A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
							elseif (Stk[Inst[2]] == Inst[4]) then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						elseif (Enum <= 31) then
							local A = Inst[2];
							Stk[A](Stk[A + 1]);
						elseif (Enum > 32) then
							for Idx = Inst[2], Inst[3] do
								Stk[Idx] = nil;
							end
						else
							local A = Inst[2];
							Stk[A](Unpack(Stk, A + 1, Top));
						end
					elseif (Enum <= 35) then
						if (Enum == 34) then
							local A = Inst[2];
							local B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
						else
							Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
						end
					elseif (Enum <= 36) then
						local A = Inst[2];
						local Results = {Stk[A](Stk[A + 1])};
						local Edx = 0;
						for Idx = A, Inst[4] do
							Edx = Edx + 1;
							Stk[Idx] = Results[Edx];
						end
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
							if (Mvm[1] == 65) then
								Indexes[Idx - 1] = {Stk,Mvm[3]};
							else
								Indexes[Idx - 1] = {Upvalues,Mvm[3]};
							end
							Lupvals[#Lupvals + 1] = Indexes;
						end
						Stk[Inst[2]] = Wrap(NewProto, NewUvals, Env);
					else
						Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
					end
				elseif (Enum <= 58) then
					if (Enum <= 48) then
						if (Enum <= 43) then
							if (Enum <= 40) then
								if (Enum == 39) then
									local B = Stk[Inst[4]];
									if not B then
										VIP = VIP + 1;
									else
										Stk[Inst[2]] = B;
										VIP = Inst[3];
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
							elseif (Enum <= 41) then
								Stk[Inst[2]] = Stk[Inst[3]];
							elseif (Enum == 42) then
								if Stk[Inst[2]] then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							elseif Stk[Inst[2]] then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						elseif (Enum <= 45) then
							if (Enum == 44) then
								for Idx = Inst[2], Inst[3] do
									Stk[Idx] = nil;
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
						elseif (Enum <= 46) then
							if not Stk[Inst[2]] then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						elseif (Enum > 47) then
							local B = Inst[3];
							local K = Stk[B];
							for Idx = B + 1, Inst[4] do
								K = K .. Stk[Idx];
							end
							Stk[Inst[2]] = K;
						else
							Stk[Inst[2]] = Inst[3] + Stk[Inst[4]];
						end
					elseif (Enum <= 53) then
						if (Enum <= 50) then
							if (Enum == 49) then
								Stk[Inst[2]] = Stk[Inst[3]] % Inst[4];
							else
								local A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Top));
							end
						elseif (Enum <= 51) then
							local A = Inst[2];
							local Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Top)));
							Top = (Limit + A) - 1;
							local Edx = 0;
							for Idx = A, Top do
								Edx = Edx + 1;
								Stk[Idx] = Results[Edx];
							end
						elseif (Enum == 52) then
							local A = Inst[2];
							Stk[A] = Stk[A](Stk[A + 1]);
						else
							Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
						end
					elseif (Enum <= 55) then
						if (Enum > 54) then
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
					elseif (Enum <= 56) then
						local A = Inst[2];
						Stk[A] = Stk[A](Stk[A + 1]);
					elseif (Enum > 57) then
						Stk[Inst[2]] = Upvalues[Inst[3]];
					else
						Stk[Inst[2]] = Inst[3];
					end
				elseif (Enum <= 68) then
					if (Enum <= 63) then
						if (Enum <= 60) then
							if (Enum > 59) then
								local A = Inst[2];
								do
									return Stk[A](Unpack(Stk, A + 1, Inst[3]));
								end
							else
								Stk[Inst[2]] = {};
							end
						elseif (Enum <= 61) then
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						elseif (Enum == 62) then
							Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
						else
							Stk[Inst[2]] = Env[Inst[3]];
						end
					elseif (Enum <= 65) then
						if (Enum == 64) then
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
						else
							Stk[Inst[2]] = Stk[Inst[3]];
						end
					elseif (Enum <= 66) then
						do
							return Stk[Inst[2]];
						end
					elseif (Enum > 67) then
						local A = Inst[2];
						do
							return Unpack(Stk, A, Top);
						end
					else
						Stk[Inst[2]] = Stk[Inst[3]] % Stk[Inst[4]];
					end
				elseif (Enum <= 73) then
					if (Enum <= 70) then
						if (Enum > 69) then
							Stk[Inst[2]] = #Stk[Inst[3]];
						else
							local A = Inst[2];
							do
								return Unpack(Stk, A, Top);
							end
						end
					elseif (Enum <= 71) then
						if (Stk[Inst[2]] == Inst[4]) then
							VIP = VIP + 1;
						else
							VIP = Inst[3];
						end
					elseif (Enum > 72) then
						Stk[Inst[2]] = Inst[3];
					else
						Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
					end
				elseif (Enum <= 75) then
					if (Enum == 74) then
						VIP = Inst[3];
					else
						Stk[Inst[2]] = #Stk[Inst[3]];
					end
				elseif (Enum <= 76) then
					local A = Inst[2];
					local Results, Limit = _R(Stk[A](Stk[A + 1]));
					Top = (Limit + A) - 1;
					local Edx = 0;
					for Idx = A, Top do
						Edx = Edx + 1;
						Stk[Idx] = Results[Edx];
					end
				elseif (Enum == 77) then
					VIP = Inst[3];
				else
					Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
				end
				VIP = VIP + 1;
			end
		end;
	end
	return Wrap(Deserialize(), {}, vmenv)(...);
end
return VMCall("LOL!163Q0003063Q00737472696E6703043Q006368617203043Q00627974652Q033Q0073756203053Q0062697433322Q033Q0062697403043Q0062786F7203053Q007461626C6503063Q00636F6E63617403063Q00696E7365727403043Q0067616D65030A3Q0047657453657276696365030B3Q00D4546CF54E4324EA497BE003073Q00569C2018851D2603083Q008B9C51A94E6559A403073Q0037C7E523C81D1C030D3Q003BC9D920077DF4DB275D60E2C803053Q0073149ABC5403083Q006973666F6C646572030A3Q006D616B65666F6C64657203043Q005361766503043Q004C6F6164003C3Q00121C3Q00013Q00203D5Q000200121C000100013Q00203D00010001000300121C000200013Q00203D00020002000400121C000300053Q00062E0003000A0001000100044A3Q000A000100121C000300063Q00203D00040003000700121C000500083Q00203D00050005000900121C000600083Q00203D00060006000A00062600073Q000100062Q00413Q00064Q00418Q00413Q00044Q00413Q00014Q00413Q00024Q00413Q00053Q00121C0008000B3Q00201400080008000C2Q0029000A00073Q001239000B000D3Q001239000C000E4Q002D000A000C4Q001D00083Q00022Q000900096Q0029000A00073Q001239000B000F3Q001239000C00104Q0001000A000C00022Q0029000B000A4Q0029000C00073Q001239000D00113Q001239000E00124Q0001000C000E00022Q000E000B000B000C00121C000C00134Q0029000D000A4Q0038000C0002000200062E000C00300001000100044A3Q0030000100121C000C00144Q0029000D000A4Q0019000C00020001000626000C0001000100032Q00413Q000B4Q00413Q00084Q00413Q00073Q00101200090015000C000626000C0002000100032Q00413Q000B4Q00413Q00084Q00413Q00073Q00101200090016000C2Q0017000900024Q00133Q00013Q00033Q00023Q00026Q00F03F026Q00704002264Q000900025Q001239000300014Q004600045Q001239000500013Q00041A0003002100012Q001B00076Q0029000800024Q001B000900014Q001B000A00024Q001B000B00034Q001B000C00044Q0029000D6Q0029000E00063Q00203E000F000600012Q002D000C000F4Q001D000B3Q00022Q001B000C00034Q001B000D00044Q0029000E00014Q0046000F00014Q0004000F0006000F00100D000F0001000F2Q0046001000014Q000400100006001000100D00100001001000203E0010001000012Q002D000D00104Q0015000C6Q001D000A3Q0002002010000A000A00022Q004C0009000A4Q002000073Q00010004370003000500012Q001B000300054Q0029000400024Q003C000300044Q004500036Q00133Q00017Q000D3Q00028Q0003053Q007063612Q6C03043Q007761726E03283Q00EAF3943E808CC8D18E11C199D0D6812985FFC5D0CD3F80A9D49F9E2995ABD8D18A6CCCFFFADA947603063Q00DFB1BFED4CE103063Q0073DBB235426A03073Q00DB36A9C05A305003083Q00746F737472696E6703053Q007072696E74032C3Q00726E19374871192B4A7F40165C4103205A510630454E19655A4316204D0213205D56092B4E024D656247197F03043Q004529226003063Q008AC2DB1F077103063Q004BDCA3B76A62032D3Q001239000300014Q002C000400053Q00261E000300020001000100044A3Q0002000100121C000600023Q00062600073Q000100042Q003A8Q003A3Q00014Q00413Q00014Q00413Q00024Q00240006000200072Q0029000500074Q0029000400063Q00062E0004001E0001000100044A3Q001E000100121C000600034Q001B000700023Q001239000800043Q001239000900054Q00010007000900022Q0029000800014Q001B000900023Q001239000A00063Q001239000B00074Q00010009000B000200121C000A00084Q0029000B00054Q004C000A000B4Q002000063Q000100044A3Q002C000100121C000600094Q001B000700023Q0012390008000A3Q0012390009000B4Q00010007000900022Q0029000800014Q001B000900023Q001239000A000C3Q001239000B000D4Q00010009000B00022Q0029000A00024Q00050006000A000100044A3Q002C000100044A3Q000200012Q00133Q00013Q00013Q00073Q00028Q00026Q00F03F03093Q00777269746566696C65030A3Q004A534F4E456E636F646503063Q00697366696C65030A3Q004A534F4E4465636F646503083Q007265616466696C6500233Q0012393Q00014Q002C000100013Q00261E3Q000C0001000200044A3Q000C000100121C000200034Q001B00036Q001B000400013Q0020140004000400042Q0029000600014Q002D000400064Q002000023Q000100044A3Q0022000100261E3Q00020001000100044A3Q0002000100121C000200054Q001B00036Q003800020002000200062A0002001B00013Q00044A3Q001B00012Q001B000200013Q00201400020002000600121C000400074Q001B00056Q004C000400054Q001D00023Q00020006270001001D0001000200044A3Q001D00012Q000900026Q0029000100024Q001B000200024Q001B000300034Q00230001000200030012393Q00023Q00044A3Q000200012Q00133Q00017Q000D3Q00028Q0003053Q007063612Q6C03053Q007072696E74032D3Q0039969225D831A38534E442899E34DA07A99831CC0EB69277D50DBB8F32DD42A98E23CD0BB48C779442918E2E8303053Q00B962DAEB5703063Q00FD3D2BF3DBF003063Q00CAAB5C4786BE03043Q007761726E03283Q0012ED359A28F235862AFC6CAE28C8208D2D81388769CD23892D813F8D3DD525862E8161C802C435D203043Q00E849A14C03063Q009ECB50520CE103053Q007EDBB9223D03083Q00746F737472696E6703373Q001239000300014Q002C000400053Q00261E000300020001000100044A3Q0002000100121C000600023Q00062600073Q000100042Q003A8Q003A3Q00014Q00413Q00014Q00413Q00024Q00240006000200072Q0029000500074Q0029000400063Q00062A0004002100013Q00044A3Q00210001001239000600013Q00261E000600100001000100044A3Q0010000100121C000700034Q001B000800023Q001239000900043Q001239000A00054Q00010008000A00022Q0029000900014Q001B000A00023Q001239000B00063Q001239000C00074Q0001000A000C00022Q0029000B00054Q00050007000B00012Q0017000500023Q00044A3Q0010000100044A3Q00360001001239000600013Q00261E000600220001000100044A3Q0022000100121C000700084Q001B000800023Q001239000900093Q001239000A000A4Q00010008000A00022Q0029000900014Q001B000A00023Q001239000B000B3Q001239000C000C4Q0001000A000C000200121C000B000D4Q0029000C00054Q004C000B000C4Q002000073Q00012Q0017000200023Q00044A3Q0022000100044A3Q0036000100044A3Q000200012Q00133Q00013Q00013Q00043Q00028Q0003063Q00697366696C65030A3Q004A534F4E4465636F646503083Q007265616466696C65001B3Q0012393Q00014Q002C000100013Q00261E3Q00020001000100044A3Q0002000100121C000200024Q001B00036Q003800020002000200062A0002001100013Q00044A3Q001100012Q001B000200013Q00201400020002000300121C000400044Q001B00056Q004C000400054Q001D00023Q0002000627000100130001000200044A3Q001300012Q000900026Q0029000100024Q001B000200024Q002500020001000200062E000200180001000100044A3Q001800012Q001B000200034Q0017000200023Q00044A3Q000200012Q00133Q00017Q00", GetFEnv(), ...);
