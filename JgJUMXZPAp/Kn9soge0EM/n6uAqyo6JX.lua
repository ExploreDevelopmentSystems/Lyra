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
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								elseif (Enum == 1) then
									Stk[Inst[2]] = Inst[3] + Stk[Inst[4]];
								else
									Stk[Inst[2]] = Env[Inst[3]];
								end
							elseif (Enum <= 4) then
								if (Enum == 3) then
									VIP = Inst[3];
								else
									local A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Top));
								end
							elseif (Enum == 5) then
								Stk[Inst[2]] = Stk[Inst[3]];
							else
								Stk[Inst[2]] = Env[Inst[3]];
							end
						elseif (Enum <= 10) then
							if (Enum <= 8) then
								if (Enum > 7) then
									local A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								else
									Stk[Inst[2]] = Stk[Inst[3]] % Stk[Inst[4]];
								end
							elseif (Enum == 9) then
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
								do
									return Stk[A](Unpack(Stk, A + 1, Inst[3]));
								end
							end
						elseif (Enum <= 12) then
							if (Enum > 11) then
								Stk[Inst[2]] = Inst[3];
							else
								local A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Top));
							end
						elseif (Enum > 13) then
							local A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
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
					elseif (Enum <= 21) then
						if (Enum <= 17) then
							if (Enum <= 15) then
								Stk[Inst[2]][Stk[Inst[3]]] = Inst[4];
							elseif (Enum > 16) then
								if not Stk[Inst[2]] then
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
						elseif (Enum <= 19) then
							if (Enum > 18) then
								do
									return Stk[Inst[2]];
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
						elseif (Enum == 20) then
							Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
						else
							Stk[Inst[2]] = {};
						end
					elseif (Enum <= 25) then
						if (Enum <= 23) then
							if (Enum > 22) then
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
									if (Mvm[1] == 34) then
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
						elseif (Enum == 24) then
							local A = Inst[2];
							local Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
							Top = (Limit + A) - 1;
							local Edx = 0;
							for Idx = A, Top do
								Edx = Edx + 1;
								Stk[Idx] = Results[Edx];
							end
						else
							Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
						end
					elseif (Enum <= 27) then
						if (Enum == 26) then
							local A = Inst[2];
							do
								return Unpack(Stk, A, A + Inst[3]);
							end
						else
							Stk[Inst[2]] = Inst[3];
						end
					elseif (Enum == 28) then
						Stk[Inst[2]] = Upvalues[Inst[3]];
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
				elseif (Enum <= 44) then
					if (Enum <= 36) then
						if (Enum <= 32) then
							if (Enum <= 30) then
								Stk[Inst[2]][Stk[Inst[3]]] = Inst[4];
							elseif (Enum > 31) then
								local A = Inst[2];
								local Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Top)));
								Top = (Limit + A) - 1;
								local Edx = 0;
								for Idx = A, Top do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
							else
								Stk[Inst[2]] = #Stk[Inst[3]];
							end
						elseif (Enum <= 34) then
							if (Enum == 33) then
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							else
								Stk[Inst[2]] = Stk[Inst[3]];
							end
						elseif (Enum > 35) then
							do
								return;
							end
						elseif not Stk[Inst[2]] then
							VIP = VIP + 1;
						else
							VIP = Inst[3];
						end
					elseif (Enum <= 40) then
						if (Enum <= 38) then
							if (Enum > 37) then
								local A = Inst[2];
								local Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Top)));
								Top = (Limit + A) - 1;
								local Edx = 0;
								for Idx = A, Top do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
							else
								Stk[Inst[2]] = Stk[Inst[3]] % Inst[4];
							end
						elseif (Enum > 39) then
							Stk[Inst[2]] = Upvalues[Inst[3]];
						else
							Stk[Inst[2]] = Inst[3] + Stk[Inst[4]];
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
							Stk[Inst[2]] = {};
						end
					elseif (Enum > 43) then
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
						Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
					end
				elseif (Enum <= 51) then
					if (Enum <= 47) then
						if (Enum <= 45) then
							do
								return Stk[Inst[2]];
							end
						elseif (Enum > 46) then
							local A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
						else
							local A = Inst[2];
							do
								return Unpack(Stk, A, Top);
							end
						end
					elseif (Enum <= 49) then
						if (Enum == 48) then
							local A = Inst[2];
							local T = Stk[A];
							local B = Inst[3];
							for Idx = 1, B do
								T[Idx] = Stk[A + Idx];
							end
						else
							do
								return;
							end
						end
					elseif (Enum == 50) then
						Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
					else
						local A = Inst[2];
						do
							return Unpack(Stk, A, Top);
						end
					end
				elseif (Enum <= 55) then
					if (Enum <= 53) then
						if (Enum > 52) then
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
							local T = Stk[A];
							for Idx = A + 1, Inst[3] do
								Insert(T, Stk[Idx]);
							end
						end
					elseif (Enum > 54) then
						local A = Inst[2];
						local T = Stk[A];
						local B = Inst[3];
						for Idx = 1, B do
							T[Idx] = Stk[A + Idx];
						end
					else
						VIP = Inst[3];
					end
				elseif (Enum <= 57) then
					if (Enum > 56) then
						Stk[Inst[2]] = Stk[Inst[3]] % Stk[Inst[4]];
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
							if (Mvm[1] == 34) then
								Indexes[Idx - 1] = {Stk,Mvm[3]};
							else
								Indexes[Idx - 1] = {Upvalues,Mvm[3]};
							end
							Lupvals[#Lupvals + 1] = Indexes;
						end
						Stk[Inst[2]] = Wrap(NewProto, NewUvals, Env);
					end
				elseif (Enum == 58) then
					Stk[Inst[2]] = Stk[Inst[3]] % Inst[4];
				else
					Stk[Inst[2]] = #Stk[Inst[3]];
				end
				VIP = VIP + 1;
			end
		end;
	end
	return Wrap(Deserialize(), {}, vmenv)(...);
end
return VMCall("LOL!3A3Q0003063Q00737472696E6703043Q006368617203043Q00627974652Q033Q0073756203053Q0062697433322Q033Q0062697403043Q0062786F7203053Q007461626C6503063Q00636F6E63617403063Q00696E73657274030C3Q00E1D1DE28EFAECA39D0CEDE3603083Q007EB1A3BB4586DBA703023Q000AC903053Q009C43AD4AA5022Q00601D9DC5FE4103043Q001AB6441303073Q002654D72976DC46030C3Q0071142B1EF7440F6225FF420503053Q009E30764272030A3Q008E3C153566B1FE9E361C03073Q009BCB44705613C503753Q004EC922EC5322AAB754DC21B24771F1F053DF23EF456AE6F748C933F25436E6F74B9213E450742QEA43F933EA4574EAE84BD838E87361F6EC43D025B36C61F7F909CF33FA5337EDFD47D925B34D79ECF609F731D67555DDC276FC26B3762CC3C215EC65F94E6CAACE12FB0CAF712BE0F652933AE94103083Q009826BD569C20188503023Q00D55303043Q00269C37C7023Q00C4FEE5944103043Q00867C712D03083Q0023C81D1C4873149A030E3Q0029ADD4D2842Q395998D0D2886C6603073Q005479DFB1BFED4C030A3Q009E4ECCA32F4435F4A95A03083Q00A1DB36A9C05A305003473Q00415614355A184F6A5B43176B4E4B142D5C4015364C50032A4756052B5D0C032A440D392A5C503220594D4F155B470D2C5C4F27244447526A4443092B065103374052146B45570103043Q004529226003093Q009AD1D20F252AB1C6C403063Q004BDCA3B76A6203023Q002BBE03053Q00B962DAEB57023Q0050C15E764103043Q00E53D2AE303063Q00CAAB5C4786BE030B3Q000FD3298D69E62D852C817D03043Q00E849A14C030A3Q009EC1475E0BAFDC774F1203053Q007EDBB9223D03443Q0004DA4A626D2DBCA81ECF493C797EE7EF19CC4B617B65F0E802DA5B7C6A39F0E80181677D6B65C1E21CC111546C72F6C00DC35B23317AF2EE02814D716C7EE3F342C24B7303083Q00876CAE3E121E179303023Q009FED03083Q00A7D6894AAB78CE53023Q00E0298C974103043Q00A5F13F5803063Q00C7EB90523D98030B3Q002104BC2E4731B8260256EB03043Q004B6776D9030A3Q00E24C7517AC0AC261621803063Q007EA7341074D903443Q00C03A3490A743B3873C2197FA1EF5DC263582A10AF9DA2D2F8EA01CF2DC60238FB956C5C73B32B2B109F387083285B13EFDC52B72CFB918F5C6613383A610ECDC602C95B503073Q009CA84E40E0D47900873Q0012063Q00013Q00206Q0002001206000100013Q00202Q000100010003001206000200013Q00202Q000200020004001206000300053Q0006230003000A000100010004033Q000A0001001206000300063Q00202Q000400030007001206000500083Q00202Q000500050009001206000600083Q00202Q00060006000A00063800073Q000100062Q00223Q00064Q00228Q00223Q00044Q00223Q00014Q00223Q00024Q00223Q00054Q002A00083Q00022Q0005000900073Q00121B000A000B3Q00121B000B000C4Q00080009000B00022Q002A000A00024Q002A000B3Q00032Q0005000C00073Q00121B000D000D3Q00121B000E000E4Q0008000C000E000200200F000B000C000F2Q0005000C00073Q00121B000D00103Q00121B000E00114Q0008000C000E00022Q0005000D00073Q00121B000E00123Q00121B000F00134Q0008000D000F00022Q0014000B000C000D2Q0005000C00073Q00121B000D00143Q00121B000E00154Q0008000C000E00022Q0005000D00073Q00121B000E00163Q00121B000F00174Q0008000D000F00022Q0014000B000C000D2Q002A000C3Q00032Q0005000D00073Q00121B000E00183Q00121B000F00194Q0008000D000F000200200F000C000D001A2Q0005000D00073Q00121B000E001B3Q00121B000F001C4Q0008000D000F00022Q0005000E00073Q00121B000F001D3Q00121B0010001E4Q0008000E001000022Q0014000C000D000E2Q0005000D00073Q00121B000E001F3Q00121B000F00204Q0008000D000F00022Q0005000E00073Q00121B000F00213Q00121B001000224Q0008000E001000022Q0014000C000D000E2Q0037000A000200012Q001400080009000A2Q0005000900073Q00121B000A00233Q00121B000B00244Q00080009000B00022Q002A000A00024Q002A000B3Q00032Q0005000C00073Q00121B000D00253Q00121B000E00264Q0008000C000E000200200F000B000C00272Q0005000C00073Q00121B000D00283Q00121B000E00294Q0008000C000E00022Q0005000D00073Q00121B000E002A3Q00121B000F002B4Q0008000D000F00022Q0014000B000C000D2Q0005000C00073Q00121B000D002C3Q00121B000E002D4Q0008000C000E00022Q0005000D00073Q00121B000E002E3Q00121B000F002F4Q0008000D000F00022Q0014000B000C000D2Q002A000C3Q00032Q0005000D00073Q00121B000E00303Q00121B000F00314Q0008000D000F000200200F000C000D00322Q0005000D00073Q00121B000E00333Q00121B000F00344Q0008000D000F00022Q0005000E00073Q00121B000F00353Q00121B001000364Q0008000E001000022Q0014000C000D000E2Q0005000D00073Q00121B000E00373Q00121B000F00384Q0008000D000F00022Q0005000E00073Q00121B000F00393Q00121B0010003A4Q0008000E001000022Q0014000C000D000E2Q0037000A000200012Q001400080009000A2Q0013000800024Q00243Q00013Q00013Q00023Q00026Q00F03F026Q00704002264Q002A00025Q00121B000300014Q001F00045Q00121B000500013Q0004350003002100012Q001C00076Q0005000800024Q001C000900014Q001C000A00024Q001C000B00034Q001C000C00044Q0005000D6Q0005000E00063Q00202B000F000600012Q0009000C000F4Q0016000B3Q00022Q001C000C00034Q001C000D00044Q0005000E00014Q001F000F00014Q0007000F0006000F001001000F0001000F2Q001F001000014Q000700100006001000100100100001001000202B0010001000012Q0009000D00104Q0026000C6Q0016000A3Q000200203A000A000A00022Q001D0009000A4Q000400073Q000100042C0003000500012Q001C000300054Q0005000400024Q000A000300044Q002E00036Q00243Q00017Q00", GetFEnv(), ...);
