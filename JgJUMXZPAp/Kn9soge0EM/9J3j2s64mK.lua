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
				if (Enum <= 29) then
					if (Enum <= 14) then
						if (Enum <= 6) then
							if (Enum <= 2) then
								if (Enum <= 0) then
									local A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Top));
								elseif (Enum > 1) then
									Stk[Inst[2]] = Inst[3] + Stk[Inst[4]];
								else
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								end
							elseif (Enum <= 4) then
								if (Enum == 3) then
									local A = Inst[2];
									do
										return Unpack(Stk, A, Top);
									end
								else
									local A = Inst[2];
									local T = Stk[A];
									local B = Inst[3];
									for Idx = 1, B do
										T[Idx] = Stk[A + Idx];
									end
								end
							elseif (Enum == 5) then
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
									if (Mvm[1] == 38) then
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
						elseif (Enum <= 10) then
							if (Enum <= 8) then
								if (Enum == 7) then
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
							elseif (Enum > 9) then
								Stk[Inst[2]][Stk[Inst[3]]] = Inst[4];
							else
								Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
							end
						elseif (Enum <= 12) then
							if (Enum == 11) then
								VIP = Inst[3];
							else
								local A = Inst[2];
								do
									return Stk[A](Unpack(Stk, A + 1, Inst[3]));
								end
							end
						elseif (Enum == 13) then
							Stk[Inst[2]] = #Stk[Inst[3]];
						else
							do
								return Stk[Inst[2]];
							end
						end
					elseif (Enum <= 21) then
						if (Enum <= 17) then
							if (Enum <= 15) then
								local A = Inst[2];
								local Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Top)));
								Top = (Limit + A) - 1;
								local Edx = 0;
								for Idx = A, Top do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
							elseif (Enum == 16) then
								Stk[Inst[2]] = Upvalues[Inst[3]];
							else
								Stk[Inst[2]] = Stk[Inst[3]] % Inst[4];
							end
						elseif (Enum <= 19) then
							if (Enum > 18) then
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
								Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
							end
						elseif (Enum > 20) then
							Stk[Inst[2]] = Inst[3] + Stk[Inst[4]];
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
					elseif (Enum <= 25) then
						if (Enum <= 23) then
							if (Enum > 22) then
								local A = Inst[2];
								local Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
								Top = (Limit + A) - 1;
								local Edx = 0;
								for Idx = A, Top do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
							else
								Stk[Inst[2]] = Env[Inst[3]];
							end
						elseif (Enum == 24) then
							Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
						else
							Stk[Inst[2]] = Stk[Inst[3]] % Inst[4];
						end
					elseif (Enum <= 27) then
						if (Enum == 26) then
							local A = Inst[2];
							do
								return Stk[A](Unpack(Stk, A + 1, Inst[3]));
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
					elseif (Enum > 28) then
						Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
					else
						local A = Inst[2];
						do
							return Unpack(Stk, A, A + Inst[3]);
						end
					end
				elseif (Enum <= 44) then
					if (Enum <= 36) then
						if (Enum <= 32) then
							if (Enum <= 30) then
								local A = Inst[2];
								do
									return Unpack(Stk, A, Top);
								end
							elseif (Enum > 31) then
								Stk[Inst[2]] = {};
							else
								local A = Inst[2];
								local T = Stk[A];
								local B = Inst[3];
								for Idx = 1, B do
									T[Idx] = Stk[A + Idx];
								end
							end
						elseif (Enum <= 34) then
							if (Enum == 33) then
								Stk[Inst[2]] = Env[Inst[3]];
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
						elseif (Enum == 35) then
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
								if (Mvm[1] == 38) then
									Indexes[Idx - 1] = {Stk,Mvm[3]};
								else
									Indexes[Idx - 1] = {Upvalues,Mvm[3]};
								end
								Lupvals[#Lupvals + 1] = Indexes;
							end
							Stk[Inst[2]] = Wrap(NewProto, NewUvals, Env);
						else
							local A = Inst[2];
							local T = Stk[A];
							for Idx = A + 1, Inst[3] do
								Insert(T, Stk[Idx]);
							end
						end
					elseif (Enum <= 40) then
						if (Enum <= 38) then
							if (Enum > 37) then
								Stk[Inst[2]] = Stk[Inst[3]];
							else
								Stk[Inst[2]] = #Stk[Inst[3]];
							end
						elseif (Enum > 39) then
							if not Stk[Inst[2]] then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						else
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						end
					elseif (Enum <= 42) then
						if (Enum == 41) then
							local A = Inst[2];
							local Results, Limit = _R(Stk[A](Stk[A + 1]));
							Top = (Limit + A) - 1;
							local Edx = 0;
							for Idx = A, Top do
								Edx = Edx + 1;
								Stk[Idx] = Results[Edx];
							end
						else
							Stk[Inst[2]][Stk[Inst[3]]] = Inst[4];
						end
					elseif (Enum == 43) then
						Stk[Inst[2]] = Upvalues[Inst[3]];
					else
						VIP = Inst[3];
					end
				elseif (Enum <= 51) then
					if (Enum <= 47) then
						if (Enum <= 45) then
							Stk[Inst[2]] = Inst[3];
						elseif (Enum > 46) then
							do
								return Stk[Inst[2]];
							end
						else
							do
								return;
							end
						end
					elseif (Enum <= 49) then
						if (Enum == 48) then
							local A = Inst[2];
							local Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
							Top = (Limit + A) - 1;
							local Edx = 0;
							for Idx = A, Top do
								Edx = Edx + 1;
								Stk[Idx] = Results[Edx];
							end
						else
							Stk[Inst[2]] = Inst[3];
						end
					elseif (Enum == 50) then
						do
							return;
						end
					else
						Stk[Inst[2]] = Stk[Inst[3]] % Stk[Inst[4]];
					end
				elseif (Enum <= 55) then
					if (Enum <= 53) then
						if (Enum > 52) then
							Stk[Inst[2]] = {};
						else
							local A = Inst[2];
							Stk[A](Unpack(Stk, A + 1, Top));
						end
					elseif (Enum == 54) then
						Stk[Inst[2]] = Stk[Inst[3]] % Stk[Inst[4]];
					else
						local A = Inst[2];
						Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
					end
				elseif (Enum <= 57) then
					if (Enum > 56) then
						local A = Inst[2];
						Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
					elseif not Stk[Inst[2]] then
						VIP = VIP + 1;
					else
						VIP = Inst[3];
					end
				elseif (Enum == 58) then
					local A = Inst[2];
					Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
				else
					Stk[Inst[2]] = Stk[Inst[3]];
				end
				VIP = VIP + 1;
			end
		end;
	end
	return Wrap(Deserialize(), {}, vmenv)(...);
end
return VMCall("LOL!173Q0003063Q00737472696E6703043Q006368617203043Q00627974652Q033Q0073756203053Q0062697433322Q033Q0062697403043Q0062786F7203053Q007461626C6503063Q00636F6E63617403063Q00696E736572742Q033Q00FAC6C203083Q007EB1A3BB4586DBA72Q033Q00729F7903053Q009C43AD4AA5030A3Q0011AF591FAE237F31B65B03073Q002654D72976DC46025Q00A89F40030B3Q00750E321BEC553B2D1CEA5803053Q009E30764272026Q00284003093Q008E3C003F61A0DFAA3D03073Q009BCB44705613C5026Q003F4000333Q0012163Q00013Q0020015Q0002001216000100013Q002001000100010003001216000200013Q002001000200020004001216000300053Q0006280003000A0001000100042C3Q000A0001001216000300063Q002001000400030007001216000500083Q002001000500050009001216000600083Q00200100060006000A00060500073Q000100062Q00263Q00064Q00268Q00263Q00044Q00263Q00014Q00263Q00024Q00263Q00054Q0035000800014Q003500093Q00042Q003B000A00073Q001231000B000B3Q001231000C000C4Q0037000A000C00022Q003B000B00073Q001231000C000D3Q001231000D000E4Q0037000B000D00022Q00180009000A000B2Q003B000A00073Q001231000B000F3Q001231000C00104Q0037000A000C000200200A0009000A00112Q003B000A00073Q001231000B00123Q001231000C00134Q0037000A000C000200200A0009000A00142Q003B000A00073Q001231000B00153Q001231000C00164Q0037000A000C000200200A0009000A00172Q001F0008000100012Q002F000800024Q002E3Q00013Q00013Q00023Q00026Q00F03F026Q00704002264Q003500025Q001231000300014Q000D00045Q001231000500013Q0004070003002100012Q002B00076Q003B000800024Q002B000900014Q002B000A00024Q002B000B00034Q002B000C00044Q003B000D6Q003B000E00063Q002009000F000600012Q0017000C000F4Q0008000B3Q00022Q002B000C00034Q002B000D00044Q003B000E00014Q000D000F00014Q0033000F0006000F001002000F0001000F2Q000D001000014Q00330010000600100010020010000100100020090010001000012Q0017000D00104Q0022000C6Q0008000A3Q0002002011000A000A00022Q00290009000A6Q00073Q000100041B0003000500012Q002B000300054Q003B000400024Q000C000300044Q000300036Q002E3Q00017Q00", GetFEnv(), ...);
