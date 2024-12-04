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
				if (Enum <= 34) then
					if (Enum <= 16) then
						if (Enum <= 7) then
							if (Enum <= 3) then
								if (Enum <= 1) then
									if (Enum > 0) then
										local A = Inst[2];
										do
											return Unpack(Stk, A, A + Inst[3]);
										end
									elseif not Stk[Inst[2]] then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								elseif (Enum > 2) then
									do
										return;
									end
								else
									Stk[Inst[2]] = #Stk[Inst[3]];
								end
							elseif (Enum <= 5) then
								if (Enum > 4) then
									Stk[Inst[2]] = Stk[Inst[3]];
								else
									Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
								end
							elseif (Enum > 6) then
								local A = Inst[2];
								do
									return Stk[A](Unpack(Stk, A + 1, Inst[3]));
								end
							elseif not Stk[Inst[2]] then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						elseif (Enum <= 11) then
							if (Enum <= 9) then
								if (Enum == 8) then
									Stk[Inst[2]] = Env[Inst[3]];
								else
									Stk[Inst[2]] = #Stk[Inst[3]];
								end
							elseif (Enum == 10) then
								local A = Inst[2];
								local Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Top)));
								Top = (Limit + A) - 1;
								local Edx = 0;
								for Idx = A, Top do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
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
						elseif (Enum <= 13) then
							if (Enum > 12) then
								local A = Inst[2];
								Stk[A] = Stk[A](Stk[A + 1]);
							else
								Stk[Inst[2]][Stk[Inst[3]]] = Inst[4];
							end
						elseif (Enum <= 14) then
							Stk[Inst[2]] = Upvalues[Inst[3]];
						elseif (Enum == 15) then
							Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
						else
							Stk[Inst[2]] = Inst[3] ~= 0;
							VIP = VIP + 1;
						end
					elseif (Enum <= 25) then
						if (Enum <= 20) then
							if (Enum <= 18) then
								if (Enum > 17) then
									local A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
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
							elseif (Enum > 19) then
								if (Stk[Inst[2]] == Inst[4]) then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							else
								Stk[Inst[2]] = {};
							end
						elseif (Enum <= 22) then
							if (Enum > 21) then
								Stk[Inst[2]] = Stk[Inst[3]];
							else
								local A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
							end
						elseif (Enum <= 23) then
							do
								return Stk[Inst[2]];
							end
						elseif (Enum > 24) then
							Stk[Inst[2]] = {};
						else
							Stk[Inst[2]] = Inst[3] ~= 0;
						end
					elseif (Enum <= 29) then
						if (Enum <= 27) then
							if (Enum > 26) then
								Stk[Inst[2]] = Env[Inst[3]];
							else
								Stk[Inst[2]] = Inst[3] ~= 0;
								VIP = VIP + 1;
							end
						elseif (Enum == 28) then
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
					elseif (Enum <= 31) then
						if (Enum > 30) then
							Stk[Inst[2]] = Inst[3];
						elseif (Stk[Inst[2]] ~= Stk[Inst[4]]) then
							VIP = VIP + 1;
						else
							VIP = Inst[3];
						end
					elseif (Enum <= 32) then
						local A = Inst[2];
						local Results, Limit = _R(Stk[A](Stk[A + 1]));
						Top = (Limit + A) - 1;
						local Edx = 0;
						for Idx = A, Top do
							Edx = Edx + 1;
							Stk[Idx] = Results[Edx];
						end
					elseif (Enum > 33) then
						VIP = Inst[3];
					else
						local A = Inst[2];
						Stk[A](Unpack(Stk, A + 1, Top));
					end
				elseif (Enum <= 51) then
					if (Enum <= 42) then
						if (Enum <= 38) then
							if (Enum <= 36) then
								if (Enum == 35) then
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								else
									local A = Inst[2];
									do
										return Stk[A](Unpack(Stk, A + 1, Inst[3]));
									end
								end
							elseif (Enum == 37) then
								local A = Inst[2];
								local T = Stk[A];
								for Idx = A + 1, Inst[3] do
									Insert(T, Stk[Idx]);
								end
							else
								Stk[Inst[2]] = Upvalues[Inst[3]];
							end
						elseif (Enum <= 40) then
							if (Enum == 39) then
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
						elseif (Enum == 41) then
							Stk[Inst[2]] = Stk[Inst[3]] % Inst[4];
						else
							local A = Inst[2];
							local T = Stk[A];
							local B = Inst[3];
							for Idx = 1, B do
								T[Idx] = Stk[A + Idx];
							end
						end
					elseif (Enum <= 46) then
						if (Enum <= 44) then
							if (Enum > 43) then
								local A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Top));
							else
								local A = Inst[2];
								Stk[A] = Stk[A](Stk[A + 1]);
							end
						elseif (Enum == 45) then
							VIP = Inst[3];
						else
							Stk[Inst[2]] = Stk[Inst[3]] % Inst[4];
						end
					elseif (Enum <= 48) then
						if (Enum > 47) then
							local A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
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
								if (Mvm[1] == 5) then
									Indexes[Idx - 1] = {Stk,Mvm[3]};
								else
									Indexes[Idx - 1] = {Upvalues,Mvm[3]};
								end
								Lupvals[#Lupvals + 1] = Indexes;
							end
							Stk[Inst[2]] = Wrap(NewProto, NewUvals, Env);
						end
					elseif (Enum <= 49) then
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
					elseif (Enum > 50) then
						Stk[Inst[2]][Stk[Inst[3]]] = Inst[4];
					else
						do
							return;
						end
					end
				elseif (Enum <= 60) then
					if (Enum <= 55) then
						if (Enum <= 53) then
							if (Enum == 52) then
								local A = Inst[2];
								do
									return Unpack(Stk, A, Top);
								end
							else
								Stk[Inst[2]] = Stk[Inst[3]] % Stk[Inst[4]];
							end
						elseif (Enum > 54) then
							Stk[Inst[2]] = Inst[3] ~= 0;
						else
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						end
					elseif (Enum <= 57) then
						if (Enum == 56) then
							Stk[Inst[2]] = Stk[Inst[3]] % Stk[Inst[4]];
						else
							Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
						end
					elseif (Enum <= 58) then
						Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
					elseif (Enum > 59) then
						if (Stk[Inst[2]] ~= Stk[Inst[4]]) then
							VIP = VIP + 1;
						else
							VIP = Inst[3];
						end
					else
						local A = Inst[2];
						local T = Stk[A];
						local B = Inst[3];
						for Idx = 1, B do
							T[Idx] = Stk[A + Idx];
						end
					end
				elseif (Enum <= 64) then
					if (Enum <= 62) then
						if (Enum > 61) then
							local A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
						else
							Stk[Inst[2]] = Inst[3];
						end
					elseif (Enum > 63) then
						local A = Inst[2];
						local Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Top)));
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
				elseif (Enum <= 66) then
					if (Enum == 65) then
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
					elseif (Stk[Inst[2]] == Inst[4]) then
						VIP = VIP + 1;
					else
						VIP = Inst[3];
					end
				elseif (Enum <= 67) then
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
				elseif (Enum == 68) then
					local A = Inst[2];
					do
						return Unpack(Stk, A, Top);
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
						if (Mvm[1] == 5) then
							Indexes[Idx - 1] = {Stk,Mvm[3]};
						else
							Indexes[Idx - 1] = {Upvalues,Mvm[3]};
						end
						Lupvals[#Lupvals + 1] = Indexes;
					end
					Stk[Inst[2]] = Wrap(NewProto, NewUvals, Env);
				end
				VIP = VIP + 1;
			end
		end;
	end
	return Wrap(Deserialize(), {}, vmenv)(...);
end
return VMCall("LOL!0C3Q0003063Q00737472696E6703043Q006368617203043Q00627974652Q033Q0073756203053Q0062697433322Q033Q0062697403043Q0062786F7203053Q007461626C6503063Q00636F6E63617403063Q00696E7365727403203Q004020E0511FB2F45460B64A23BBD4671EBE5341A5DB5E6D946D4FEBC25F16E14303073Q00B32654D72976DC00213Q0012083Q00013Q0020235Q0002001208000100013Q002023000100010003001208000200013Q002023000200020004001208000300053Q00062Q0003000A000100010004223Q000A0001001208000300063Q002023000400030007001208000500083Q002023000500050009001208000600083Q00202300060006000A00062F00073Q000100062Q00053Q00064Q00058Q00053Q00044Q00053Q00014Q00053Q00024Q00053Q00054Q0016000800073Q00121F0009000B3Q00121F000A000C4Q00120008000A000200062F00090001000100012Q00053Q00083Q00062F000A0002000100022Q00053Q00094Q00053Q00074Q003F000A00024Q00033Q00013Q00033Q00023Q00026Q00F03F026Q00704002264Q001300025Q00121F000300014Q000900045Q00121F000500013Q0004410003002100012Q002600076Q0016000800024Q0026000900014Q0026000A00024Q0026000B00034Q0026000C00044Q0016000D6Q0016000E00063Q00200F000F000600012Q001D000C000F4Q003E000B3Q00022Q0026000C00034Q0026000D00044Q0016000E00014Q0009000F00014Q0035000F0006000F001027000F0001000F2Q0009001000014Q003500100006001000102700100001001000200F0010001000012Q001D000D00104Q0040000C6Q003E000A3Q000200202E000A000A00022Q00280009000A4Q002100073Q00010004310003000500012Q0026000300054Q0016000400024Q0007000300044Q003400036Q00033Q00019Q002Q0001074Q002600015Q00061E3Q0004000100010004223Q000400012Q001000016Q0037000100014Q003F000100024Q00033Q00017Q00263Q00028Q0003053Q00652Q726F7203243Q00D75E002322F75456232DFD5505316EEA5F1D2720B01037212DFB4305622AFB5E1F272AB003053Q004E9E3076422Q033Q00D0AE3D03063Q00B69BCB4470562Q033Q00EFAA1503043Q00C5DE982603023Q00D57003073Q00569C2018851D26030E3Q00F0D60DF9242C19F6D31AE62C2F2Q03073Q0037C7E523C81D1C030A3Q0051E2CC3D0171C3D9350103053Q0073149ABC54025Q00A89F40030B3Q00F4C79D2593BAFCD083388903063Q00DFB1BFED4CE1026Q00284003093Q0073D1B03342359F57D003073Q00DB36A9C05A3050026Q003F402Q033Q0062471903043Q004529226003063Q0084FAED5E577D03063Q004BDCA3B76A6203023Q002B8A03053Q00B962DAEB57030E3Q009C6F69B787FA856D71BF90FB986803063Q00CAAB5C4786BE030A3Q000CD93C813BC4158D28D303043Q00E849A14C025Q00989F40030B3Q009EC152540CBEF44D530AB303053Q007EDBB9223D026Q00F03F03093Q0029D64E7B6C72D7E61503083Q00876CAE3E121E1793026Q002E4001573Q00121F000100013Q00261400010001000100010004223Q000100012Q002600026Q001600036Q002B00020002000200062Q0002000E000100010004223Q000E0001001208000200024Q0026000300013Q00121F000400033Q00121F000500044Q001D000300054Q002100023Q00012Q0013000200024Q001300033Q00052Q0026000400013Q00121F000500053Q00121F000600064Q00120004000600022Q0026000500013Q00121F000600073Q00121F000700084Q00120005000700022Q003A0003000400052Q0026000400013Q00121F000500093Q00121F0006000A4Q00120004000600022Q0026000500013Q00121F0006000B3Q00121F0007000C4Q00120005000700022Q003A0003000400052Q0026000400013Q00121F0005000D3Q00121F0006000E4Q001200040006000200203300030004000F2Q0026000400013Q00121F000500103Q00121F000600114Q00120004000600020020330003000400122Q0026000400013Q00121F000500133Q00121F000600144Q00120004000600020020330003000400152Q001300043Q00052Q0026000500013Q00121F000600163Q00121F000700174Q00120005000700022Q0026000600013Q00121F000700183Q00121F000800194Q00120006000800022Q003A0004000500062Q0026000500013Q00121F0006001A3Q00121F0007001B4Q00120005000700022Q0026000600013Q00121F0007001C3Q00121F0008001D4Q00120006000800022Q003A0004000500062Q0026000500013Q00121F0006001E3Q00121F0007001F4Q00120005000700020020330004000500202Q0026000500013Q00121F000600213Q00121F000700224Q00120005000700020020330004000500232Q0026000500013Q00121F000600243Q00121F000700254Q00120005000700020020330004000500262Q002A0002000200012Q003F000200023Q0004223Q000100012Q00033Q00017Q00", GetFEnv(), ...);
