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
										Stk[Inst[2]] = #Stk[Inst[3]];
									else
										local A = Inst[2];
										Stk[A](Unpack(Stk, A + 1, Top));
									end
								elseif (Enum == 2) then
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
									Stk[A] = Stk[A]();
								end
							elseif (Enum <= 5) then
								if (Enum == 4) then
									local A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
								else
									local A = Inst[2];
									local B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
								end
							elseif (Enum <= 6) then
								Stk[Inst[2]] = Env[Inst[3]];
							elseif (Enum > 7) then
								Stk[Inst[2]] = {};
							else
								Stk[Inst[2]] = Inst[3];
							end
						elseif (Enum <= 12) then
							if (Enum <= 10) then
								if (Enum > 9) then
									if Stk[Inst[2]] then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								else
									local A = Inst[2];
									Stk[A] = Stk[A]();
								end
							elseif (Enum > 11) then
								local A = Inst[2];
								do
									return Unpack(Stk, A, Top);
								end
							else
								Stk[Inst[2]] = Inst[3] + Stk[Inst[4]];
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
								Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
							end
						elseif (Enum <= 15) then
							Stk[Inst[2]] = Stk[Inst[3]];
						elseif (Enum > 16) then
							do
								return;
							end
						else
							Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
						end
					elseif (Enum <= 26) then
						if (Enum <= 21) then
							if (Enum <= 19) then
								if (Enum == 18) then
									local A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Top));
								else
									VIP = Inst[3];
								end
							elseif (Enum > 20) then
								Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
							else
								local A = Inst[2];
								local B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
							end
						elseif (Enum <= 23) then
							if (Enum == 22) then
								if Stk[Inst[2]] then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							else
								Stk[Inst[2]] = #Stk[Inst[3]];
							end
						elseif (Enum <= 24) then
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						elseif (Enum == 25) then
							Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
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
								if (Mvm[1] == 15) then
									Indexes[Idx - 1] = {Stk,Mvm[3]};
								else
									Indexes[Idx - 1] = {Upvalues,Mvm[3]};
								end
								Lupvals[#Lupvals + 1] = Indexes;
							end
							Stk[Inst[2]] = Wrap(NewProto, NewUvals, Env);
						end
					elseif (Enum <= 31) then
						if (Enum <= 28) then
							if (Enum == 27) then
								local A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
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
						elseif (Enum <= 29) then
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
								if (Mvm[1] == 15) then
									Indexes[Idx - 1] = {Stk,Mvm[3]};
								else
									Indexes[Idx - 1] = {Upvalues,Mvm[3]};
								end
								Lupvals[#Lupvals + 1] = Indexes;
							end
							Stk[Inst[2]] = Wrap(NewProto, NewUvals, Env);
						elseif (Enum == 30) then
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
					elseif (Enum <= 33) then
						if (Enum == 32) then
							local A = Inst[2];
							Stk[A](Unpack(Stk, A + 1, Inst[3]));
						else
							Stk[Inst[2]] = Upvalues[Inst[3]];
						end
					elseif (Enum <= 34) then
						Stk[Inst[2]] = Stk[Inst[3]] % Inst[4];
					elseif (Enum == 35) then
						Stk[Inst[2]] = Env[Inst[3]];
					else
						Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
					end
				elseif (Enum <= 55) then
					if (Enum <= 45) then
						if (Enum <= 40) then
							if (Enum <= 38) then
								if (Enum > 37) then
									Stk[Inst[2]] = Stk[Inst[3]];
								else
									for Idx = Inst[2], Inst[3] do
										Stk[Idx] = nil;
									end
								end
							elseif (Enum == 39) then
								do
									return Stk[Inst[2]];
								end
							else
								Stk[Inst[2]] = Stk[Inst[3]] % Stk[Inst[4]];
							end
						elseif (Enum <= 42) then
							if (Enum == 41) then
								Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
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
						elseif (Enum <= 43) then
							local A = Inst[2];
							do
								return Unpack(Stk, A, Top);
							end
						elseif (Enum > 44) then
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
					elseif (Enum <= 50) then
						if (Enum <= 47) then
							if (Enum > 46) then
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							else
								local A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
							end
						elseif (Enum <= 48) then
							Stk[Inst[2]] = Inst[3];
						elseif (Enum > 49) then
							for Idx = Inst[2], Inst[3] do
								Stk[Idx] = nil;
							end
						else
							VIP = Inst[3];
						end
					elseif (Enum <= 52) then
						if (Enum == 51) then
							Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
						else
							do
								return;
							end
						end
					elseif (Enum <= 53) then
						Stk[Inst[2]] = Stk[Inst[3]] % Stk[Inst[4]];
					elseif (Enum == 54) then
						local A = Inst[2];
						Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
					else
						local B = Stk[Inst[4]];
						if not B then
							VIP = VIP + 1;
						else
							Stk[Inst[2]] = B;
							VIP = Inst[3];
						end
					end
				elseif (Enum <= 64) then
					if (Enum <= 59) then
						if (Enum <= 57) then
							if (Enum > 56) then
								local B = Stk[Inst[4]];
								if not B then
									VIP = VIP + 1;
								else
									Stk[Inst[2]] = B;
									VIP = Inst[3];
								end
							else
								Stk[Inst[2]] = Upvalues[Inst[3]];
							end
						elseif (Enum == 58) then
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
					elseif (Enum <= 61) then
						if (Enum == 60) then
							local A = Inst[2];
							Stk[A] = Stk[A](Stk[A + 1]);
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
					elseif (Enum <= 62) then
						if not Stk[Inst[2]] then
							VIP = VIP + 1;
						else
							VIP = Inst[3];
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
						Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
					end
				elseif (Enum <= 69) then
					if (Enum <= 66) then
						if (Enum > 65) then
							if (Stk[Inst[2]] == Inst[4]) then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						else
							local A = Inst[2];
							do
								return Stk[A](Unpack(Stk, A + 1, Inst[3]));
							end
						end
					elseif (Enum <= 67) then
						local A = Inst[2];
						do
							return Unpack(Stk, A, A + Inst[3]);
						end
					elseif (Enum == 68) then
						Stk[Inst[2]] = Stk[Inst[3]] % Inst[4];
					else
						Stk[Inst[2]] = Inst[3] + Stk[Inst[4]];
					end
				elseif (Enum <= 71) then
					if (Enum == 70) then
						if not Stk[Inst[2]] then
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
				elseif (Enum <= 72) then
					if (Stk[Inst[2]] == Inst[4]) then
						VIP = VIP + 1;
					else
						VIP = Inst[3];
					end
				elseif (Enum == 73) then
					local A = Inst[2];
					do
						return Stk[A](Unpack(Stk, A + 1, Inst[3]));
					end
				else
					local A = Inst[2];
					Stk[A] = Stk[A](Stk[A + 1]);
				end
				VIP = VIP + 1;
			end
		end;
	end
	return Wrap(Deserialize(), {}, vmenv)(...);
end
return VMCall("LOL!143Q0003063Q00737472696E6703043Q006368617203043Q00627974652Q033Q0073756203053Q0062697433322Q033Q0062697403043Q0062786F7203053Q007461626C6503063Q00636F6E63617403063Q00696E7365727403073Q007265717569726503063Q0073637269707403063Q00506172656E7403083Q004C79726153796E63030A3Q006C6F6164737472696E6703043Q0067616D6503073Q00482Q7470476574031C3Q002E3AEA4005E66961ED5904B5333DB05D13B23361EC510FBA2F2BF25403063Q00DC464E9E307603063Q00437265617465002D3Q0012063Q00013Q0020185Q0002001206000100013Q002018000100010003001206000200013Q002018000200020004001206000300053Q00063E0003000A000100010004133Q000A0001001206000300063Q002018000400030007001206000500083Q002018000500050009001206000600083Q00201800060006000A00061A00073Q000100062Q000F3Q00064Q000F8Q000F3Q00044Q000F3Q00014Q000F3Q00024Q000F3Q00053Q0012060008000B3Q0012060009000C3Q00201800090009000D00201800090009000E2Q004A0008000200022Q002D00095Q001206000A000F3Q001206000B00103Q002005000B000B00112Q0026000D00073Q001207000E00123Q001207000F00134Q002A000D000F4Q003D000B6Q0036000A3Q00022Q0003000A0001000200061A000B0001000100032Q000F3Q000A4Q000F3Q00074Q000F3Q00083Q00102400090014000B2Q0027000900024Q00343Q00013Q00023Q00023Q00026Q00F03F026Q00704002264Q002D00025Q001207000300014Q001700045Q001207000500013Q00040D0003002100012Q002100076Q0026000800024Q0021000900014Q0021000A00024Q0021000B00034Q0021000C00044Q0026000D6Q0026000E00063Q002029000F000600012Q002A000C000F4Q0036000B3Q00022Q0021000C00034Q0021000D00044Q0026000E00014Q0017000F00014Q0028000F0006000F00100B000F0001000F2Q0017001000014Q002800100006001000100B0010000100100020290010001000012Q002A000D00104Q003D000C6Q0036000A3Q0002002044000A000A00022Q003A0009000A4Q000100073Q000100042C0003000500012Q0021000300054Q0026000400024Q0041000300044Q002B00036Q00343Q00017Q00233Q00028Q00027Q004003063Q004E6F7469667903053Q00E2F2BF281703053Q0072B69BCB4403073Q0050AAB0EC43386703063Q005613C5DE982603083Q00D8556AE4694F39F203073Q00569C2018851D2603053Q008E8842AF7803073Q0037C7E523C81D1C026Q00F03F03043Q004C6F616403143Q005AF5C83D157DF9DD201A7BF4F8210175EED53B1D03053Q0073149ABC54026Q001A4003053Q006C6F77657203043Q00D8D18B2303063Q00DFB1BFED4CE103053Q0053DBB2354203073Q00DB36A9C05A3050030C3Q004F4B0C2004550137474B0E2203043Q004529226003073Q00ABC2C5040B25BB03063Q004BDCA3B76A62030E3Q0016A88236D705B68E7AD80EBF992303053Q00B962DAEB5703043Q00C23221E903063Q00CAAB5C4786BE03043Q0020CF2A8703043Q00E849A14C03093Q00BFDC56581DAFD04D5303053Q007EDBB9223D030C3Q001FC657777273BEE600CB4C6603083Q00876CAE3E121E179305613Q001207000500014Q0032000600083Q0026420005001D000100020004133Q001D00012Q002100095Q0020050009000900032Q002D000B3Q00042Q0021000C00013Q001207000D00043Q001207000E00054Q001E000C000E00022Q0010000B000C00032Q0021000C00013Q001207000D00063Q001207000E00074Q001E000C000E00022Q0010000B000C00042Q0021000C00013Q001207000D00083Q001207000E00094Q001E000C000E00022Q0010000B000C00072Q0021000C00013Q001207000D000A3Q001207000E000B4Q001E000C000E00022Q0010000B000C00082Q00040009000B00010004133Q00600001002642000500350001000C0004133Q003500010006160002002A00013Q0004133Q002A00012Q0021000900023Q00200500090009000D2Q0021000B00013Q001207000C000E3Q001207000D000F4Q001E000B000D0002001207000C00104Q001E0009000C00022Q0026000700093Q0020050009000100112Q004A0009000200022Q001900090006000900063700080034000100090004133Q003400012Q0021000900013Q001207000A00123Q001207000B00134Q001E0009000B00022Q0026000800093Q001207000500023Q00264200050002000100010004133Q000200012Q002D00093Q00042Q0021000A00013Q001207000B00143Q001207000C00154Q001E000A000C00022Q0021000B00013Q001207000C00163Q001207000D00174Q001E000B000D00022Q00100009000A000B2Q0021000A00013Q001207000B00183Q001207000C00194Q001E000A000C00022Q0021000B00013Q001207000C001A3Q001207000D001B4Q001E000B000D00022Q00100009000A000B2Q0021000A00013Q001207000B001C3Q001207000C001D4Q001E000A000C00022Q0021000B00013Q001207000C001E3Q001207000D001F4Q001E000B000D00022Q00100009000A000B2Q0021000A00013Q001207000B00203Q001207000C00214Q001E000A000C00022Q0021000B00013Q001207000C00223Q001207000D00234Q001E000B000D00022Q00100009000A000B2Q0026000600093Q001207000700103Q0012070005000C3Q0004133Q000200012Q00343Q00017Q00", GetFEnv(), ...);
