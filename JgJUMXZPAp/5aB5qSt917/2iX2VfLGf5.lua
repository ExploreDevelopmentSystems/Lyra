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
										do
											return Unpack(Stk, A, Top);
										end
									else
										VIP = Inst[3];
									end
								elseif (Enum > 2) then
									local A = Inst[2];
									local Results = {Stk[A](Stk[A + 1])};
									local Edx = 0;
									for Idx = A, Inst[4] do
										Edx = Edx + 1;
										Stk[Idx] = Results[Edx];
									end
								else
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								end
							elseif (Enum <= 5) then
								if (Enum > 4) then
									for Idx = Inst[2], Inst[3] do
										Stk[Idx] = nil;
									end
								else
									for Idx = Inst[2], Inst[3] do
										Stk[Idx] = nil;
									end
								end
							elseif (Enum <= 6) then
								Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
							elseif (Enum > 7) then
								local A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							else
								local A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							end
						elseif (Enum <= 13) then
							if (Enum <= 10) then
								if (Enum > 9) then
									local B = Inst[3];
									local K = Stk[B];
									for Idx = B + 1, Inst[4] do
										K = K .. Stk[Idx];
									end
									Stk[Inst[2]] = K;
								else
									Stk[Inst[2]] = Inst[3] + Stk[Inst[4]];
								end
							elseif (Enum <= 11) then
								local B = Stk[Inst[4]];
								if not B then
									VIP = VIP + 1;
								else
									Stk[Inst[2]] = B;
									VIP = Inst[3];
								end
							elseif (Enum > 12) then
								Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
							else
								Stk[Inst[2]] = Stk[Inst[3]];
							end
						elseif (Enum <= 15) then
							if (Enum > 14) then
								Stk[Inst[2]] = Env[Inst[3]];
							elseif (Stk[Inst[2]] == Inst[4]) then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						elseif (Enum <= 16) then
							Stk[Inst[2]] = {};
						elseif (Enum > 17) then
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
							local Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Top)));
							Top = (Limit + A) - 1;
							local Edx = 0;
							for Idx = A, Top do
								Edx = Edx + 1;
								Stk[Idx] = Results[Edx];
							end
						end
					elseif (Enum <= 28) then
						if (Enum <= 23) then
							if (Enum <= 20) then
								if (Enum == 19) then
									if Stk[Inst[2]] then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								else
									Stk[Inst[2]] = Inst[3];
								end
							elseif (Enum <= 21) then
								Stk[Inst[2]] = Stk[Inst[3]];
							elseif (Enum > 22) then
								Stk[Inst[2]] = Stk[Inst[3]] % Inst[4];
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
							if (Enum > 24) then
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
								Stk[Inst[2]] = Upvalues[Inst[3]];
							end
						elseif (Enum <= 26) then
							if (Stk[Inst[2]] == Inst[4]) then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						elseif (Enum == 27) then
							local A = Inst[2];
							local Results, Limit = _R(Stk[A](Stk[A + 1]));
							Top = (Limit + A) - 1;
							local Edx = 0;
							for Idx = A, Top do
								Edx = Edx + 1;
								Stk[Idx] = Results[Edx];
							end
						elseif (Stk[Inst[2]] == Stk[Inst[4]]) then
							VIP = VIP + 1;
						else
							VIP = Inst[3];
						end
					elseif (Enum <= 33) then
						if (Enum <= 30) then
							if (Enum == 29) then
								Stk[Inst[2]] = #Stk[Inst[3]];
							else
								Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
							end
						elseif (Enum <= 31) then
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
								if (Mvm[1] == 12) then
									Indexes[Idx - 1] = {Stk,Mvm[3]};
								else
									Indexes[Idx - 1] = {Upvalues,Mvm[3]};
								end
								Lupvals[#Lupvals + 1] = Indexes;
							end
							Stk[Inst[2]] = Wrap(NewProto, NewUvals, Env);
						elseif (Enum == 32) then
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
					elseif (Enum <= 35) then
						if (Enum > 34) then
							VIP = Inst[3];
						else
							local A = Inst[2];
							Stk[A](Unpack(Stk, A + 1, Top));
						end
					elseif (Enum <= 36) then
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
							if (Mvm[1] == 12) then
								Indexes[Idx - 1] = {Stk,Mvm[3]};
							else
								Indexes[Idx - 1] = {Upvalues,Mvm[3]};
							end
							Lupvals[#Lupvals + 1] = Indexes;
						end
						Stk[Inst[2]] = Wrap(NewProto, NewUvals, Env);
					elseif (Enum > 37) then
						Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
					else
						Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
					end
				elseif (Enum <= 58) then
					if (Enum <= 48) then
						if (Enum <= 43) then
							if (Enum <= 40) then
								if (Enum > 39) then
									local A = Inst[2];
									Stk[A] = Stk[A](Stk[A + 1]);
								else
									local A = Inst[2];
									local B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
								end
							elseif (Enum <= 41) then
								Stk[Inst[2]] = Stk[Inst[3]] % Stk[Inst[4]];
							elseif (Enum > 42) then
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
						elseif (Enum <= 45) then
							if (Enum == 44) then
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
						elseif (Enum <= 46) then
							Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
						elseif (Enum > 47) then
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
					elseif (Enum <= 53) then
						if (Enum <= 50) then
							if (Enum > 49) then
								local A = Inst[2];
								Stk[A](Stk[A + 1]);
							else
								Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
							end
						elseif (Enum <= 51) then
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						elseif (Enum == 52) then
							local A = Inst[2];
							Stk[A](Unpack(Stk, A + 1, Top));
						else
							Stk[Inst[2]] = Env[Inst[3]];
						end
					elseif (Enum <= 55) then
						if (Enum > 54) then
							if not Stk[Inst[2]] then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
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
					elseif (Enum <= 56) then
						local A = Inst[2];
						local Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
						Top = (Limit + A) - 1;
						local Edx = 0;
						for Idx = A, Top do
							Edx = Edx + 1;
							Stk[Idx] = Results[Edx];
						end
					elseif (Enum > 57) then
						Stk[Inst[2]] = Inst[3] + Stk[Inst[4]];
					elseif not Stk[Inst[2]] then
						VIP = VIP + 1;
					else
						VIP = Inst[3];
					end
				elseif (Enum <= 68) then
					if (Enum <= 63) then
						if (Enum <= 60) then
							if (Enum > 59) then
								do
									return Stk[Inst[2]];
								end
							else
								local A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
							end
						elseif (Enum <= 61) then
							local A = Inst[2];
							do
								return Unpack(Stk, A, Top);
							end
						elseif (Enum > 62) then
							local A = Inst[2];
							Stk[A] = Stk[A](Stk[A + 1]);
						else
							local A = Inst[2];
							do
								return Stk[A](Unpack(Stk, A + 1, Inst[3]));
							end
						end
					elseif (Enum <= 65) then
						if (Enum > 64) then
							do
								return Stk[Inst[2]];
							end
						else
							local A = Inst[2];
							do
								return Stk[A](Unpack(Stk, A + 1, Inst[3]));
							end
						end
					elseif (Enum <= 66) then
						local A = Inst[2];
						Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
					elseif (Enum > 67) then
						if (Stk[Inst[2]] == Stk[Inst[4]]) then
							VIP = VIP + 1;
						else
							VIP = Inst[3];
						end
					else
						Stk[Inst[2]] = Upvalues[Inst[3]];
					end
				elseif (Enum <= 73) then
					if (Enum <= 70) then
						if (Enum == 69) then
							Stk[Inst[2]] = Stk[Inst[3]] % Inst[4];
						else
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						end
					elseif (Enum <= 71) then
						local A = Inst[2];
						do
							return Unpack(Stk, A, A + Inst[3]);
						end
					elseif (Enum == 72) then
						do
							return;
						end
					else
						do
							return;
						end
					end
				elseif (Enum <= 75) then
					if (Enum > 74) then
						Stk[Inst[2]] = {};
					else
						local A = Inst[2];
						local B = Stk[Inst[3]];
						Stk[A + 1] = B;
						Stk[A] = B[Inst[4]];
					end
				elseif (Enum <= 76) then
					local A = Inst[2];
					Stk[A](Stk[A + 1]);
				elseif (Enum == 77) then
					Stk[Inst[2]] = Stk[Inst[3]] % Stk[Inst[4]];
				else
					Stk[Inst[2]] = Inst[3];
				end
				VIP = VIP + 1;
			end
		end;
	end
	return Wrap(Deserialize(), {}, vmenv)(...);
end
return VMCall("LOL!163Q0003063Q00737472696E6703043Q006368617203043Q00627974652Q033Q0073756203053Q0062697433322Q033Q0062697403043Q0062786F7203053Q007461626C6503063Q00636F6E63617403063Q00696E7365727403043Q0067616D65030A3Q0047657453657276696365030B3Q001EE854CD05F952CB3FFF4503043Q00BD569C2003083Q00515FEEE44E5FF2E603043Q00851D269C030D3Q00CA70ADB3914AA6A0960DBCBF9103043Q00C7E523C803083Q006973666F6C646572030A3Q006D616B65666F6C64657203043Q005361766503043Q004C6F6164003C3Q00120F3Q00013Q0020335Q000200120F000100013Q00203300010001000300120F000200013Q00203300020002000400120F000300053Q0006370003000A000100010004013Q000A000100120F000300063Q00203300040003000700120F000500083Q00203300050005000900120F000600083Q00203300060006000A00061F00073Q000100062Q000C3Q00064Q000C8Q000C3Q00044Q000C3Q00014Q000C3Q00024Q000C3Q00053Q00120F0008000B3Q00204A00080008000C2Q0015000A00073Q001214000B000D3Q001214000C000E4Q0038000A000C4Q003B00083Q00022Q004B00096Q0015000A00073Q001214000B000F3Q001214000C00104Q0008000A000C00022Q0015000B000A4Q0015000C00073Q001214000D00113Q001214000E00124Q0008000C000E00022Q000A000B000B000C00120F000C00134Q0015000D000A4Q0028000C00020002000637000C0030000100010004013Q0030000100120F000C00144Q0015000D000A4Q0032000C0002000100061F000C0001000100032Q000C3Q000B4Q000C3Q00084Q000C3Q00073Q00102600090015000C00061F000C0002000100032Q000C3Q00074Q000C3Q000B4Q000C3Q00083Q00102600090016000C2Q0041000900024Q00493Q00013Q00033Q00023Q00026Q00F03F026Q00704002264Q004B00025Q001214000300014Q001D00045Q001214000500013Q00042D0003002100012Q004300076Q0015000800024Q0043000900014Q0043000A00024Q0043000B00034Q0043000C00044Q0015000D6Q0015000E00063Q002031000F000600012Q0038000C000F4Q003B000B3Q00022Q0043000C00034Q0043000D00044Q0015000E00014Q001D000F00014Q004D000F0006000F00103A000F0001000F2Q001D001000014Q004D00100006001000103A0010000100100020310010001000012Q0038000D00104Q0011000C6Q003B000A3Q0002002045000A000A00022Q001B0009000A4Q002200073Q000100042C0003000500012Q0043000300054Q0015000400024Q0040000300044Q003D00036Q00493Q00017Q00083Q00028Q0003053Q007063612Q6C03043Q007761726E03283Q00133F6D6E29206D722B2E345A291A78792C5360736800756A2D5367793C077D722F53393C03166D2603043Q001C48731403063Q00110BADDECDD703073Q00BC5479DFB1BFED03083Q00746F737472696E6703203Q001214000300014Q0004000400053Q00260E00030002000100010004013Q0002000100120F000600023Q00061F00073Q000100042Q00188Q00183Q00014Q000C3Q00014Q000C3Q00024Q00030006000200072Q0015000500074Q0015000400063Q0006370004001F000100010004013Q001F000100120F000600034Q0043000700023Q001214000800043Q001214000900054Q00080007000900022Q0015000800014Q0043000900023Q001214000A00063Q001214000B00074Q00080009000B000200120F000A00084Q0015000B00054Q001B000A000B4Q002200063Q00010004013Q001F00010004013Q000200012Q00493Q00013Q00013Q00073Q00028Q00026Q00F03F03093Q00777269746566696C65030A3Q004A534F4E456E636F646503063Q00697366696C65030A3Q004A534F4E4465636F646503083Q007265616466696C6500233Q0012143Q00014Q0004000100013Q00260E3Q000C000100020004013Q000C000100120F000200034Q004300036Q0043000400013Q00204A0004000400042Q0015000600014Q0038000400064Q002200023Q00010004013Q0022000100260E3Q0002000100010004013Q0002000100120F000200054Q004300036Q00280002000200020006130002001B00013Q0004013Q001B00012Q0043000200013Q00204A00020002000600120F000400074Q004300056Q001B000400054Q003B00023Q000200060B0001001D000100020004013Q001D00012Q004B00026Q0015000100024Q0043000200024Q0043000300034Q000D0001000200030012143Q00023Q0004013Q000200012Q00493Q00017Q00083Q00028Q0003053Q007063612Q6C03043Q007761726E03283Q006B1C4C374871235E3368656F43335C3551655D4D7A5C3F542109513F44245C2B4E0277101B503C1303073Q005A30503545292203063Q000EAED1D8E17103053Q00934BDCA3B703083Q00746F737472696E6703283Q001214000300014Q0004000400053Q00260E00030002000100010004013Q0002000100120F000600023Q00061F00073Q000100052Q00188Q000C3Q00024Q00183Q00014Q00183Q00024Q000C3Q00014Q00030006000200072Q0015000500074Q0015000400063Q0006130004001200013Q0004013Q001200012Q0041000500023Q0004013Q00270001001214000600013Q00260E00060013000100010004013Q0013000100120F000700034Q004300085Q001214000900043Q001214000A00054Q00080008000A00022Q0015000900014Q0043000A5Q001214000B00063Q001214000C00074Q0008000A000C000200120F000B00084Q0015000C00054Q001B000B000C4Q002200073Q00012Q0041000200023Q0004013Q001300010004013Q002700010004013Q000200012Q00493Q00013Q00013Q00083Q00028Q00026Q00F03F03063Q00747970656F6603053Q00D5BA54C58403053Q00E1A1DB36A903063Q00697366696C65030A3Q004A534F4E4465636F646503083Q007265616466696C65002B3Q0012143Q00014Q0004000100023Q00260E3Q0015000100020004013Q0015000100120F000300034Q0015000400024Q00280003000200022Q004300045Q001214000500043Q001214000600054Q000800040006000200064400030011000100040004013Q001100012Q001D000300023Q00260E00030011000100020004013Q0011000100203300020002000200060B00030014000100020004013Q001400012Q0043000300014Q0041000300023Q00260E3Q0002000100010004013Q0002000100120F000300064Q0043000400024Q00280003000200020006130003002400013Q0004013Q002400012Q0043000300033Q00204A00030003000700120F000500084Q0043000600024Q001B000500064Q003B00033Q000200060B00010026000100030004013Q002600012Q004B00036Q0015000100034Q0043000300044Q001E0002000100030012143Q00023Q0004013Q000200012Q00493Q00017Q00", GetFEnv(), ...);
