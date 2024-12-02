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
				if (Enum <= 35) then
					if (Enum <= 17) then
						if (Enum <= 8) then
							if (Enum <= 3) then
								if (Enum <= 1) then
									if (Enum > 0) then
										Stk[Inst[2]] = #Stk[Inst[3]];
									else
										local A = Inst[2];
										Stk[A](Unpack(Stk, A + 1, Top));
									end
								elseif (Enum > 2) then
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
							elseif (Enum <= 5) then
								if (Enum > 4) then
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
							elseif (Enum <= 6) then
								Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
							elseif (Enum == 7) then
								do
									return;
								end
							else
								local A = Inst[2];
								do
									return Unpack(Stk, A, A + Inst[3]);
								end
							end
						elseif (Enum <= 12) then
							if (Enum <= 10) then
								if (Enum == 9) then
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
							elseif (Enum > 11) then
								local A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							else
								Stk[Inst[2]] = Stk[Inst[3]] % Stk[Inst[4]];
							end
						elseif (Enum <= 14) then
							if (Enum == 13) then
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
						elseif (Enum <= 15) then
							Stk[Inst[2]] = Inst[3];
						elseif (Enum > 16) then
							Stk[Inst[2]] = {};
						else
							local A = Inst[2];
							Stk[A](Unpack(Stk, A + 1, Top));
						end
					elseif (Enum <= 26) then
						if (Enum <= 21) then
							if (Enum <= 19) then
								if (Enum > 18) then
									local A = Inst[2];
									Stk[A] = Stk[A](Stk[A + 1]);
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
										if (Mvm[1] == 71) then
											Indexes[Idx - 1] = {Stk,Mvm[3]};
										else
											Indexes[Idx - 1] = {Upvalues,Mvm[3]};
										end
										Lupvals[#Lupvals + 1] = Indexes;
									end
									Stk[Inst[2]] = Wrap(NewProto, NewUvals, Env);
								end
							elseif (Enum == 20) then
								local A = Inst[2];
								Stk[A] = Stk[A](Stk[A + 1]);
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
						elseif (Enum <= 23) then
							if (Enum > 22) then
								local A = Inst[2];
								do
									return Stk[A](Unpack(Stk, A + 1, Inst[3]));
								end
							else
								Stk[Inst[2]] = Inst[3];
							end
						elseif (Enum <= 24) then
							Stk[Inst[2]] = Inst[3] + Stk[Inst[4]];
						elseif (Enum == 25) then
							Stk[Inst[2]] = Env[Inst[3]];
						else
							Stk[Inst[2]] = Env[Inst[3]];
						end
					elseif (Enum <= 30) then
						if (Enum <= 28) then
							if (Enum > 27) then
								VIP = Inst[3];
							else
								local A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							end
						elseif (Enum == 29) then
							local A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
						else
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						end
					elseif (Enum <= 32) then
						if (Enum == 31) then
							Stk[Inst[2]] = Upvalues[Inst[3]];
						else
							local A = Inst[2];
							do
								return Unpack(Stk, A, Top);
							end
						end
					elseif (Enum <= 33) then
						local A = Inst[2];
						local Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Top)));
						Top = (Limit + A) - 1;
						local Edx = 0;
						for Idx = A, Top do
							Edx = Edx + 1;
							Stk[Idx] = Results[Edx];
						end
					elseif (Enum > 34) then
						Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
					elseif not Stk[Inst[2]] then
						VIP = VIP + 1;
					else
						VIP = Inst[3];
					end
				elseif (Enum <= 53) then
					if (Enum <= 44) then
						if (Enum <= 39) then
							if (Enum <= 37) then
								if (Enum > 36) then
									Stk[Inst[2]] = {};
								else
									local A = Inst[2];
									do
										return Stk[A](Unpack(Stk, A + 1, Inst[3]));
									end
								end
							elseif (Enum > 38) then
								Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
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
						elseif (Enum <= 41) then
							if (Enum == 40) then
								if not Stk[Inst[2]] then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							else
								local A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
							end
						elseif (Enum <= 42) then
							Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
						elseif (Enum == 43) then
							Stk[Inst[2]] = Stk[Inst[3]] % Inst[4];
						else
							local B = Stk[Inst[4]];
							if not B then
								VIP = VIP + 1;
							else
								Stk[Inst[2]] = B;
								VIP = Inst[3];
							end
						end
					elseif (Enum <= 48) then
						if (Enum <= 46) then
							if (Enum == 45) then
								Stk[Inst[2]] = Stk[Inst[3]];
							else
								VIP = Inst[3];
							end
						elseif (Enum == 47) then
							if Stk[Inst[2]] then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
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
					elseif (Enum <= 50) then
						if (Enum == 49) then
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
								if (Mvm[1] == 71) then
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
					elseif (Enum <= 51) then
						do
							return Stk[Inst[2]];
						end
					elseif (Enum > 52) then
						Stk[Inst[2]] = Stk[Inst[3]] % Inst[4];
					else
						Stk[Inst[2]] = Upvalues[Inst[3]];
					end
				elseif (Enum <= 62) then
					if (Enum <= 57) then
						if (Enum <= 55) then
							if (Enum == 54) then
								Stk[Inst[2]] = #Stk[Inst[3]];
							else
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							end
						elseif (Enum == 56) then
							local A = Inst[2];
							local B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
						else
							local A = Inst[2];
							do
								return Unpack(Stk, A, Top);
							end
						end
					elseif (Enum <= 59) then
						if (Enum > 58) then
							for Idx = Inst[2], Inst[3] do
								Stk[Idx] = nil;
							end
						else
							local A = Inst[2];
							Stk[A](Unpack(Stk, A + 1, Inst[3]));
						end
					elseif (Enum <= 60) then
						Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
					elseif (Enum == 61) then
						for Idx = Inst[2], Inst[3] do
							Stk[Idx] = nil;
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
				elseif (Enum <= 67) then
					if (Enum <= 64) then
						if (Enum == 63) then
							Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
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
					elseif (Enum <= 65) then
						do
							return;
						end
					elseif (Enum == 66) then
						do
							return Stk[Inst[2]];
						end
					else
						Stk[Inst[2]] = Stk[Inst[3]] % Stk[Inst[4]];
					end
				elseif (Enum <= 69) then
					if (Enum > 68) then
						Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
					elseif (Stk[Inst[2]] == Inst[4]) then
						VIP = VIP + 1;
					else
						VIP = Inst[3];
					end
				elseif (Enum <= 70) then
					local A = Inst[2];
					local B = Stk[Inst[3]];
					Stk[A + 1] = B;
					Stk[A] = B[Inst[4]];
				elseif (Enum > 71) then
					Stk[Inst[2]] = Inst[3] + Stk[Inst[4]];
				else
					Stk[Inst[2]] = Stk[Inst[3]];
				end
				VIP = VIP + 1;
			end
		end;
	end
	return Wrap(Deserialize(), {}, vmenv)(...);
end
return VMCall("LOL!0F3Q0003063Q00737472696E6703043Q006368617203043Q00627974652Q033Q0073756203053Q0062697433322Q033Q0062697403043Q0062786F7203053Q007461626C6503063Q00636F6E63617403063Q00696E7365727403073Q007265717569726503063Q0073637269707403063Q00506172656E7403083Q004C79726153796E6303063Q0043726561746500223Q00121A3Q00013Q0020235Q000200121A000100013Q00202300010001000300121A000200013Q00202300020002000400121A000300053Q0006280003000A0001000100041C3Q000A000100121A000300063Q00202300040003000700121A000500083Q00202300050005000900121A000600083Q00202300060006000A00063100073Q000100062Q00473Q00064Q00478Q00473Q00044Q00473Q00014Q00473Q00024Q00473Q00053Q00121A0008000B3Q00121A0009000C3Q00202300090009000D00202300090009000E2Q00140008000200022Q002500095Q000631000A0001000100022Q00473Q00074Q00473Q00083Q0010370009000F000A2Q0033000900024Q00413Q00013Q00023Q00023Q00026Q00F03F026Q00704002264Q002500025Q001216000300014Q000100045Q001216000500013Q0004300003002100012Q001F00076Q002D000800024Q001F000900014Q001F000A00024Q001F000B00034Q001F000C00044Q002D000D6Q002D000E00063Q002027000F000600012Q0032000C000F4Q000E000B3Q00022Q001F000C00034Q001F000D00044Q002D000E00014Q0001000F00014Q000B000F0006000F001048000F0001000F2Q0001001000014Q000B0010000600100010480010000100100020270010001000012Q0032000D00104Q0021000C6Q000E000A3Q000200202B000A000A00022Q00400009000A4Q001000073Q000100043E0003000500012Q001F000300054Q002D000400024Q0017000300044Q003900036Q00413Q00017Q00233Q00028Q0003053Q004C04AE29A503053Q00D72976DC46030C3Q00561F2E17B34717301CF75E1103053Q009E3076427203073Q00BC2502387AABFC03073Q009BCB44705613C5030E3Q0052CF3FFD4E7FE9FD0BDC3AF9526C03083Q009826BD569C20188503043Q00F559A14903043Q00269C37C703043Q00A1737A2703083Q0023C81D1C4873149A03093Q001DBAC5DA8E383D16B103073Q005479DFB1BFED4C030C3Q00A85EC0A536547DC0B753DBB403083Q00A1DB36A9C05A3050026Q001A40026Q00F03F03043Q004C6F616403143Q00674D142C4F4B03245D4B0F2B6D5712245D4B0F2B03043Q004529226003053Q006C6F77657203043Q00B5CDD10503063Q004BDCA3B76A62027Q004003063Q004E6F7469667903053Q0036B39F3BDC03053Q00B962DAEB5703073Q00E83329F2DBA4DF03063Q00CAAB5C4786BE03083Q000DD43E893DC8238603043Q00E849A14C03053Q0092D4435A1B03053Q007EDBB9223D06603Q001216000600014Q003D000700093Q0026020006002C0001000100041C3Q002C00012Q0025000A3Q00042Q001F000B5Q001216000C00023Q001216000D00034Q000C000B000D00022Q001F000C5Q001216000D00043Q001216000E00054Q000C000C000E00022Q002A000A000B000C2Q001F000B5Q001216000C00063Q001216000D00074Q000C000B000D00022Q001F000C5Q001216000D00083Q001216000E00094Q000C000C000E00022Q002A000A000B000C2Q001F000B5Q001216000C000A3Q001216000D000B4Q000C000B000D00022Q001F000C5Q001216000D000C3Q001216000E000D4Q000C000C000E00022Q002A000A000B000C2Q001F000B5Q001216000C000E3Q001216000D000F4Q000C000B000D00022Q001F000C5Q001216000D00103Q001216000E00114Q000C000C000E00022Q002A000A000B000C2Q002D0007000A3Q001216000800123Q001216000600133Q002602000600440001001300041C3Q004400010006030003003900013Q00041C3Q003900012Q001F000A00013Q002038000A000A00142Q001F000C5Q001216000D00153Q001216000E00164Q000C000C000E0002001216000D00124Q000C000A000D00022Q002D0008000A3Q002038000A000200172Q0014000A000200022Q0005000A0007000A000604000900430001000A00041C3Q004300012Q001F000A5Q001216000B00183Q001216000C00194Q000C000A000C00022Q002D0009000A3Q0012160006001A3Q002602000600020001001A00041C3Q00020001002038000A0001001B2Q0025000C3Q00042Q001F000D5Q001216000E001C3Q001216000F001D4Q000C000D000F00022Q002A000C000D00042Q001F000D5Q001216000E001E3Q001216000F001F4Q000C000D000F00022Q002A000C000D00052Q001F000D5Q001216000E00203Q001216000F00214Q000C000D000F00022Q002A000C000D00082Q001F000D5Q001216000E00223Q001216000F00234Q000C000D000F00022Q002A000C000D00092Q0029000A000C000100041C3Q005F000100041C3Q000200012Q00413Q00017Q00", GetFEnv(), ...);
