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
									do
										return Unpack(Stk, A, Top);
									end
								elseif (Enum > 1) then
									Stk[Inst[2]][Stk[Inst[3]]] = Inst[4];
								else
									local A = Inst[2];
									local T = Stk[A];
									local B = Inst[3];
									for Idx = 1, B do
										T[Idx] = Stk[A + Idx];
									end
								end
							elseif (Enum <= 4) then
								if (Enum == 3) then
									local A = Inst[2];
									local T = Stk[A];
									for Idx = A + 1, Inst[3] do
										Insert(T, Stk[Idx]);
									end
								else
									Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
								end
							elseif (Enum > 5) then
								Stk[Inst[2]] = Stk[Inst[3]] % Stk[Inst[4]];
							elseif not Stk[Inst[2]] then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						elseif (Enum <= 10) then
							if (Enum <= 8) then
								if (Enum == 7) then
									Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
								else
									Stk[Inst[2]] = Stk[Inst[3]] % Inst[4];
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
								Stk[Inst[2]] = #Stk[Inst[3]];
							end
						elseif (Enum <= 12) then
							if (Enum > 11) then
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
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
						elseif (Enum > 13) then
							local A = Inst[2];
							do
								return Unpack(Stk, A, Top);
							end
						else
							VIP = Inst[3];
						end
					elseif (Enum <= 21) then
						if (Enum <= 17) then
							if (Enum <= 15) then
								local A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
							elseif (Enum == 16) then
								Stk[Inst[2]] = Stk[Inst[3]] % Stk[Inst[4]];
							else
								local A = Inst[2];
								do
									return Stk[A](Unpack(Stk, A + 1, Inst[3]));
								end
							end
						elseif (Enum <= 19) then
							if (Enum == 18) then
								Stk[Inst[2]] = Stk[Inst[3]];
							else
								Stk[Inst[2]] = Stk[Inst[3]];
							end
						elseif (Enum > 20) then
							Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
						else
							local A = Inst[2];
							do
								return Unpack(Stk, A, A + Inst[3]);
							end
						end
					elseif (Enum <= 25) then
						if (Enum <= 23) then
							if (Enum == 22) then
								do
									return Stk[Inst[2]];
								end
							else
								do
									return;
								end
							end
						elseif (Enum > 24) then
							local A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
						else
							Stk[Inst[2]] = Inst[3] + Stk[Inst[4]];
						end
					elseif (Enum <= 27) then
						if (Enum > 26) then
							Stk[Inst[2]] = {};
						else
							do
								return Stk[Inst[2]];
							end
						end
					elseif (Enum == 28) then
						local A = Inst[2];
						local Results, Limit = _R(Stk[A](Stk[A + 1]));
						Top = (Limit + A) - 1;
						local Edx = 0;
						for Idx = A, Top do
							Edx = Edx + 1;
							Stk[Idx] = Results[Edx];
						end
					else
						Stk[Inst[2]] = Inst[3];
					end
				elseif (Enum <= 44) then
					if (Enum <= 36) then
						if (Enum <= 32) then
							if (Enum <= 30) then
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
							elseif (Enum == 31) then
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
									if (Mvm[1] == 18) then
										Indexes[Idx - 1] = {Stk,Mvm[3]};
									else
										Indexes[Idx - 1] = {Upvalues,Mvm[3]};
									end
									Lupvals[#Lupvals + 1] = Indexes;
								end
								Stk[Inst[2]] = Wrap(NewProto, NewUvals, Env);
							else
								Stk[Inst[2]] = #Stk[Inst[3]];
							end
						elseif (Enum <= 34) then
							if (Enum == 33) then
								local A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Top));
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
						elseif (Enum == 35) then
							Stk[Inst[2]] = Inst[3] + Stk[Inst[4]];
						else
							Stk[Inst[2]][Stk[Inst[3]]] = Inst[4];
						end
					elseif (Enum <= 40) then
						if (Enum <= 38) then
							if (Enum == 37) then
								local A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
							else
								do
									return;
								end
							end
						elseif (Enum == 39) then
							Stk[Inst[2]] = Upvalues[Inst[3]];
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
					elseif (Enum <= 42) then
						if (Enum == 41) then
							Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
						elseif not Stk[Inst[2]] then
							VIP = VIP + 1;
						else
							VIP = Inst[3];
						end
					elseif (Enum > 43) then
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
							if (Mvm[1] == 18) then
								Indexes[Idx - 1] = {Stk,Mvm[3]};
							else
								Indexes[Idx - 1] = {Upvalues,Mvm[3]};
							end
							Lupvals[#Lupvals + 1] = Indexes;
						end
						Stk[Inst[2]] = Wrap(NewProto, NewUvals, Env);
					end
				elseif (Enum <= 51) then
					if (Enum <= 47) then
						if (Enum <= 45) then
							local A = Inst[2];
							local Results, Limit = _R(Stk[A](Stk[A + 1]));
							Top = (Limit + A) - 1;
							local Edx = 0;
							for Idx = A, Top do
								Edx = Edx + 1;
								Stk[Idx] = Results[Edx];
							end
						elseif (Enum == 46) then
							Stk[Inst[2]] = Inst[3];
						else
							Stk[Inst[2]] = {};
						end
					elseif (Enum <= 49) then
						if (Enum == 48) then
							Stk[Inst[2]] = Stk[Inst[3]] % Inst[4];
						else
							local A = Inst[2];
							Stk[A](Unpack(Stk, A + 1, Top));
						end
					elseif (Enum == 50) then
						Stk[Inst[2]] = Env[Inst[3]];
					else
						Stk[Inst[2]] = Upvalues[Inst[3]];
					end
				elseif (Enum <= 55) then
					if (Enum <= 53) then
						if (Enum > 52) then
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
					elseif (Enum > 54) then
						local A = Inst[2];
						do
							return Stk[A](Unpack(Stk, A + 1, Inst[3]));
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
				elseif (Enum <= 57) then
					if (Enum == 56) then
						local A = Inst[2];
						local T = Stk[A];
						local B = Inst[3];
						for Idx = 1, B do
							T[Idx] = Stk[A + Idx];
						end
					else
						Stk[Inst[2]] = Env[Inst[3]];
					end
				elseif (Enum == 58) then
					Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
				else
					VIP = Inst[3];
				end
				VIP = VIP + 1;
			end
		end;
	end
	return Wrap(Deserialize(), {}, vmenv)(...);
end
return VMCall("LOL!2B3Q0003063Q00737472696E6703043Q006368617203043Q00627974652Q033Q0073756203053Q0062697433322Q033Q0062697403043Q0062786F7203053Q007461626C6503063Q00636F6E63617403063Q00696E736572742Q033Q00FAC6C203083Q007EB1A3BB4586DBA72Q033Q00729F7903053Q009C43AD4AA503023Q001D8703073Q002654D72976DC46030E3Q0007456C43A700587344A71E47714103053Q009E30764272030A3Q008E3C003F61A0C2AE250203073Q009BCB44705613C5025Q00A89F40030B3Q0063C526F5527DC8F748C93E03083Q009826BD569C201885026Q00284003093Q00D94FB74FEE528347E503043Q00269C37C7026Q003F402Q033Q0083786503083Q0023C81D1C4873149A03063Q002186EB8BD87A03073Q005479DFB1BFED4C03023Q00926603083Q00A1DB36A9C05A3050030E3Q001E114E7410124E741F1B4E741A1603043Q0045292260030A3Q0099DBC703102E85C6D61803063Q004BDCA3B76A62030B3Q0027A29B3ECB07978439CD0A03053Q00B962DAEB57026Q00F03F03093Q00EE2437EFCCAFEF3D3E03063Q00CAAB5C4786BE026Q002E40005E3Q0012323Q00013Q00200C5Q0002001232000100013Q00200C000100010003001232000200013Q00200C000200020004001232000300053Q00062A0003000A0001000100040D3Q000A0001001232000300063Q00200C000400030007001232000500083Q00200C000500050009001232000600083Q00200C00060006000A00061F00073Q000100062Q00123Q00064Q00128Q00123Q00044Q00123Q00014Q00123Q00024Q00123Q00054Q001B000800024Q001B00093Q00052Q0013000A00073Q00121D000B000B3Q00121D000C000C4Q0019000A000C00022Q0013000B00073Q00121D000C000D3Q00121D000D000E4Q0019000B000D00022Q00040009000A000B2Q0013000A00073Q00121D000B000F3Q00121D000C00104Q0019000A000C00022Q0013000B00073Q00121D000C00113Q00121D000D00124Q0019000B000D00022Q00040009000A000B2Q0013000A00073Q00121D000B00133Q00121D000C00144Q0019000A000C00020020240009000A00152Q0013000A00073Q00121D000B00163Q00121D000C00174Q0019000A000C00020020240009000A00182Q0013000A00073Q00121D000B00193Q00121D000C001A4Q0019000A000C00020020240009000A001B2Q001B000A3Q00052Q0013000B00073Q00121D000C001C3Q00121D000D001D4Q0019000B000D00022Q0013000C00073Q00121D000D001E3Q00121D000E001F4Q0019000C000E00022Q0004000A000B000C2Q0013000B00073Q00121D000C00203Q00121D000D00214Q0019000B000D00022Q0013000C00073Q00121D000D00223Q00121D000E00234Q0019000C000E00022Q0004000A000B000C2Q0013000B00073Q00121D000C00243Q00121D000D00254Q0019000B000D0002002024000A000B00152Q0013000B00073Q00121D000C00263Q00121D000D00274Q0019000B000D0002002024000A000B00282Q0013000B00073Q00121D000C00293Q00121D000D002A4Q0019000B000D0002002024000A000B002B2Q00010008000200012Q001A000800024Q00263Q00013Q00013Q00023Q00026Q00F03F026Q00704002264Q001B00025Q00121D000300014Q000A00045Q00121D000500013Q00041E0003002100012Q003300076Q0013000800024Q0033000900014Q0033000A00024Q0033000B00034Q0033000C00044Q0013000D6Q0013000E00063Q002007000F000600012Q0009000C000F4Q000F000B3Q00022Q0033000C00034Q0033000D00044Q0013000E00014Q000A000F00014Q0010000F0006000F001018000F0001000F2Q000A001000014Q00100010000600100010180010000100100020070010001000012Q0009000D00104Q000B000C6Q000F000A3Q0002002030000A000A00022Q001C0009000A4Q002100073Q00010004340003000500012Q0033000300054Q0013000400024Q0011000300044Q000E00036Q00263Q00017Q00", GetFEnv(), ...);
