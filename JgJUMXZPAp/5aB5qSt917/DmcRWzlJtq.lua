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
				if (Enum <= 37) then
					if (Enum <= 18) then
						if (Enum <= 8) then
							if (Enum <= 3) then
								if (Enum <= 1) then
									if (Enum > 0) then
										local A = Inst[2];
										local Results, Limit = _R(Stk[A](Stk[A + 1]));
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
								elseif (Enum > 2) then
									Stk[Inst[2]] = Stk[Inst[3]];
								else
									do
										return Stk[Inst[2]];
									end
								end
							elseif (Enum <= 5) then
								if (Enum == 4) then
									local A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Top));
								else
									Stk[Inst[2]] = Stk[Inst[3]] % Stk[Inst[4]];
								end
							elseif (Enum <= 6) then
								local A = Inst[2];
								Stk[A] = Stk[A](Stk[A + 1]);
							elseif (Enum > 7) then
								local A = Inst[2];
								do
									return Stk[A](Unpack(Stk, A + 1, Inst[3]));
								end
							else
								local A = Inst[2];
								Stk[A](Stk[A + 1]);
							end
						elseif (Enum <= 13) then
							if (Enum <= 10) then
								if (Enum > 9) then
									local B = Stk[Inst[4]];
									if not B then
										VIP = VIP + 1;
									else
										Stk[Inst[2]] = B;
										VIP = Inst[3];
									end
								else
									local A = Inst[2];
									local B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
								end
							elseif (Enum <= 11) then
								local A = Inst[2];
								do
									return Unpack(Stk, A, A + Inst[3]);
								end
							elseif (Enum > 12) then
								Stk[Inst[2]] = Inst[3] + Stk[Inst[4]];
							else
								Stk[Inst[2]] = Upvalues[Inst[3]];
							end
						elseif (Enum <= 15) then
							if (Enum == 14) then
								Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
							else
								local B = Stk[Inst[4]];
								if not B then
									VIP = VIP + 1;
								else
									Stk[Inst[2]] = B;
									VIP = Inst[3];
								end
							end
						elseif (Enum <= 16) then
							do
								return Stk[Inst[2]];
							end
						elseif (Enum > 17) then
							Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
						elseif Stk[Inst[2]] then
							VIP = VIP + 1;
						else
							VIP = Inst[3];
						end
					elseif (Enum <= 27) then
						if (Enum <= 22) then
							if (Enum <= 20) then
								if (Enum > 19) then
									do
										return;
									end
								elseif not Stk[Inst[2]] then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							elseif (Enum == 21) then
								Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
							else
								local A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
							end
						elseif (Enum <= 24) then
							if (Enum > 23) then
								Stk[Inst[2]] = #Stk[Inst[3]];
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
						elseif (Enum <= 25) then
							Stk[Inst[2]] = Stk[Inst[3]];
						elseif (Enum == 26) then
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
								if (Mvm[1] == 3) then
									Indexes[Idx - 1] = {Stk,Mvm[3]};
								else
									Indexes[Idx - 1] = {Upvalues,Mvm[3]};
								end
								Lupvals[#Lupvals + 1] = Indexes;
							end
							Stk[Inst[2]] = Wrap(NewProto, NewUvals, Env);
						else
							Stk[Inst[2]] = Inst[3];
						end
					elseif (Enum <= 32) then
						if (Enum <= 29) then
							if (Enum == 28) then
								local A = Inst[2];
								local Results = {Stk[A](Stk[A + 1])};
								local Edx = 0;
								for Idx = A, Inst[4] do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
							else
								Stk[Inst[2]] = Stk[Inst[3]] % Inst[4];
							end
						elseif (Enum <= 30) then
							VIP = Inst[3];
						elseif (Enum > 31) then
							Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
						else
							local A = Inst[2];
							Stk[A](Stk[A + 1]);
						end
					elseif (Enum <= 34) then
						if (Enum == 33) then
							local A = Inst[2];
							local Results, Limit = _R(Stk[A](Stk[A + 1]));
							Top = (Limit + A) - 1;
							local Edx = 0;
							for Idx = A, Top do
								Edx = Edx + 1;
								Stk[Idx] = Results[Edx];
							end
						else
							Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
						end
					elseif (Enum <= 35) then
						Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
					elseif (Enum == 36) then
						Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
					else
						local A = Inst[2];
						Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
					end
				elseif (Enum <= 56) then
					if (Enum <= 46) then
						if (Enum <= 41) then
							if (Enum <= 39) then
								if (Enum > 38) then
									local A = Inst[2];
									local B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
								else
									Stk[Inst[2]] = Inst[3] + Stk[Inst[4]];
								end
							elseif (Enum > 40) then
								local A = Inst[2];
								local Results = {Stk[A](Stk[A + 1])};
								local Edx = 0;
								for Idx = A, Inst[4] do
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
						elseif (Enum <= 43) then
							if (Enum > 42) then
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
									if (Mvm[1] == 3) then
										Indexes[Idx - 1] = {Stk,Mvm[3]};
									else
										Indexes[Idx - 1] = {Upvalues,Mvm[3]};
									end
									Lupvals[#Lupvals + 1] = Indexes;
								end
								Stk[Inst[2]] = Wrap(NewProto, NewUvals, Env);
							end
						elseif (Enum <= 44) then
							local A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
						elseif (Enum > 45) then
							local A = Inst[2];
							Stk[A](Unpack(Stk, A + 1, Top));
						else
							Stk[Inst[2]] = Inst[3];
						end
					elseif (Enum <= 51) then
						if (Enum <= 48) then
							if (Enum == 47) then
								VIP = Inst[3];
							else
								Stk[Inst[2]] = Env[Inst[3]];
							end
						elseif (Enum <= 49) then
							local A = Inst[2];
							do
								return Unpack(Stk, A, Top);
							end
						elseif (Enum == 50) then
							if not Stk[Inst[2]] then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						else
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
						end
					elseif (Enum <= 53) then
						if (Enum == 52) then
							Stk[Inst[2]] = {};
						else
							Stk[Inst[2]] = #Stk[Inst[3]];
						end
					elseif (Enum <= 54) then
						Stk[Inst[2]] = Stk[Inst[3]] % Inst[4];
					elseif (Enum == 55) then
						local A = Inst[2];
						do
							return Stk[A](Unpack(Stk, A + 1, Inst[3]));
						end
					elseif (Stk[Inst[2]] == Inst[4]) then
						VIP = VIP + 1;
					else
						VIP = Inst[3];
					end
				elseif (Enum <= 66) then
					if (Enum <= 61) then
						if (Enum <= 58) then
							if (Enum > 57) then
								local A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
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
						elseif (Enum <= 59) then
							do
								return;
							end
						elseif (Enum == 60) then
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
							local Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Top)));
							Top = (Limit + A) - 1;
							local Edx = 0;
							for Idx = A, Top do
								Edx = Edx + 1;
								Stk[Idx] = Results[Edx];
							end
						end
					elseif (Enum <= 63) then
						if (Enum == 62) then
							if (Stk[Inst[2]] == Inst[4]) then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						else
							Stk[Inst[2]] = Env[Inst[3]];
						end
					elseif (Enum <= 64) then
						Stk[Inst[2]] = Stk[Inst[3]] % Stk[Inst[4]];
					elseif (Enum > 65) then
						Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
					else
						local A = Inst[2];
						do
							return Unpack(Stk, A, Top);
						end
					end
				elseif (Enum <= 71) then
					if (Enum <= 68) then
						if (Enum > 67) then
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
							local B = Inst[3];
							local K = Stk[B];
							for Idx = B + 1, Inst[4] do
								K = K .. Stk[Idx];
							end
							Stk[Inst[2]] = K;
						end
					elseif (Enum <= 69) then
						Stk[Inst[2]] = {};
					elseif (Enum > 70) then
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
					elseif Stk[Inst[2]] then
						VIP = VIP + 1;
					else
						VIP = Inst[3];
					end
				elseif (Enum <= 73) then
					if (Enum > 72) then
						Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
					else
						for Idx = Inst[2], Inst[3] do
							Stk[Idx] = nil;
						end
					end
				elseif (Enum <= 74) then
					local A = Inst[2];
					Stk[A] = Stk[A](Stk[A + 1]);
				elseif (Enum > 75) then
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
				VIP = VIP + 1;
			end
		end;
	end
	return Wrap(Deserialize(), {}, vmenv)(...);
end
return VMCall("LOL!163Q0003063Q00737472696E6703043Q006368617203043Q00627974652Q033Q0073756203053Q0062697433322Q033Q0062697403043Q0062786F7203053Q007461626C6503063Q00636F6E63617403063Q00696E7365727403043Q0067616D65030A3Q0047657453657276696365030B3Q00D052C926CF456AA8F145D803083Q00DE9826BD569C201803083Q006AE545A6B66448FF03063Q001D269C37C7E5030D3Q00324F2DBC697526AF6E323CB06903043Q00C81D1C4803083Q006973666F6C646572030A3Q006D616B65666F6C646572030B3Q005361766553652Q74696E67030B3Q004C6F616453652Q74696E67003C3Q00123F3Q00013Q0020235Q000200123F000100013Q00202300010001000300123F000200013Q00202300020002000400123F000300053Q0006130003000A0001000100042F3Q000A000100123F000300063Q00202300040003000700123F000500083Q00202300050005000900123F000600083Q00202300060006000A00061A00073Q000100062Q00033Q00064Q00038Q00033Q00044Q00033Q00014Q00033Q00024Q00033Q00053Q00123F0008000B3Q00200900080008000C2Q0019000A00073Q00122D000B000D3Q00122D000C000E4Q004C000A000C4Q002500083Q00022Q0019000900073Q00122D000A000F3Q00122D000B00104Q002C0009000B00022Q0019000A00094Q0019000B00073Q00122D000C00113Q00122D000D00124Q002C000B000D00022Q0028000A000A000B00123F000B00134Q0019000C00094Q004A000B00020002000613000B002F0001000100042F3Q002F000100123F000B00144Q0019000C00094Q001F000B000200012Q0045000B5Q00061A000C0001000100032Q00033Q000A4Q00033Q00084Q00033Q00073Q001049000B0015000C00061A000C0002000100032Q00033Q000A4Q00033Q00084Q00033Q00073Q001049000B0016000C2Q0002000B00024Q003B3Q00013Q00033Q00023Q00026Q00F03F026Q00704002264Q004500025Q00122D000300014Q003500045Q00122D000500013Q0004470003002100012Q004B00076Q0019000800024Q004B000900014Q004B000A00024Q004B000B00034Q004B000C00044Q0019000D6Q0019000E00063Q002Q20000F000600012Q004C000C000F4Q0025000B3Q00022Q004B000C00034Q004B000D00044Q0019000E00014Q0035000F00014Q0005000F0006000F001026000F0001000F2Q0035001000014Q0005001000060010001026001000010010002Q200010001000012Q004C000D00104Q0039000C6Q0025000A3Q000200201D000A000A00022Q00010009000A4Q002E00073Q00010004170003000500012Q004B000300054Q0019000400024Q0037000300044Q003100036Q003B3Q00017Q00083Q00028Q0003053Q007063612Q6C03043Q007761726E03293Q00C1EF310DAB7DF4DB2731BE7AFED0310B8234DCDD3D15BA70BAC83B59AC75ECD9740ABA60EED53A1EE503063Q00149ABC5479DF03063Q00A83E93CEA90C03073Q00BFED4CE1A1DB3603083Q00746F737472696E6703203Q00122D000300016Q000400053Q00263E000300020001000100042F3Q0002000100123F000600023Q00061A00073Q000100042Q000C8Q000C3Q00014Q00033Q00014Q00033Q00024Q001C0006000200072Q0019000500074Q0019000400063Q0006130004001F0001000100042F3Q001F000100123F000600034Q004B000700023Q00122D000800043Q00122D000900054Q002C0007000900022Q0019000800014Q004B000900023Q00122D000A00063Q00122D000B00074Q002C0009000B000200123F000A00084Q0019000B00054Q0001000A000B4Q002E00063Q000100042F3Q001F000100042F3Q000200012Q003B3Q00013Q00013Q00073Q00028Q00026Q00F03F03093Q00777269746566696C65030A3Q004A534F4E456E636F646503063Q00697366696C65030A3Q004A534F4E4465636F646503083Q007265616466696C6500233Q00122D3Q00016Q000100013Q00263E3Q000C0001000200042F3Q000C000100123F000200034Q004B00036Q004B000400013Q0020090004000400042Q0019000600014Q004C000400064Q002E00023Q000100042F3Q0022000100263E3Q00020001000100042F3Q0002000100123F000200054Q004B00036Q004A0002000200020006460002001B00013Q00042F3Q001B00012Q004B000200013Q00200900020002000600123F000400074Q004B00056Q0001000400054Q002500023Q000200060F0001001D0001000200042F3Q001D00012Q004500026Q0019000100024Q004B000200024Q004B000300034Q002400010002000300122D3Q00023Q00042F3Q000200012Q003B3Q00017Q00083Q00028Q0003053Q007063612Q6C03043Q007761726E03293Q00016335413140AE3D4318542B4DAC3F420D150348A9365534153146E0365F3151655AA52E44395B221303073Q00C05A305035452903063Q00D639AE0FE17103043Q0060934BDC03083Q00746F737472696E6703273Q00122D000300016Q000400053Q00263E000300020001000100042F3Q0002000100123F000600023Q00061A00073Q000100042Q000C8Q000C3Q00014Q00033Q00014Q00033Q00024Q001C0006000200072Q0019000500074Q0019000400063Q0006460004001100013Q00042F3Q001100012Q0002000500023Q00042F3Q0026000100122D000600013Q00263E000600120001000100042F3Q0012000100123F000700034Q004B000800023Q00122D000900043Q00122D000A00054Q002C0008000A00022Q0019000900014Q004B000A00023Q00122D000B00063Q00122D000C00074Q002C000A000C000200123F000B00084Q0019000C00054Q0001000B000C4Q002E00073Q00012Q0002000200023Q00042F3Q0012000100042F3Q0026000100042F3Q000200012Q003B3Q00013Q00013Q00043Q00028Q0003063Q00697366696C65030A3Q004A534F4E4465636F646503083Q007265616466696C65001B3Q00122D3Q00016Q000100013Q00263E3Q00020001000100042F3Q0002000100123F000200024Q004B00036Q004A0002000200020006460002001100013Q00042F3Q001100012Q004B000200013Q00200900020002000300123F000400044Q004B00056Q0001000400054Q002500023Q000200060F000100130001000200042F3Q001300012Q004500026Q0019000100024Q004B000200024Q0012000200010002000613000200180001000100042F3Q001800012Q004B000200034Q0002000200023Q00042F3Q000200012Q003B3Q00017Q00", GetFEnv(), ...);
