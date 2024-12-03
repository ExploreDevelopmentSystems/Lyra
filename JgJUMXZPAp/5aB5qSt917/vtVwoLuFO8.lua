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
				if (Enum <= 46) then
					if (Enum <= 22) then
						if (Enum <= 10) then
							if (Enum <= 4) then
								if (Enum <= 1) then
									if (Enum == 0) then
										Stk[Inst[2]] = Stk[Inst[3]] % Inst[4];
									else
										local A = Inst[2];
										Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									end
								elseif (Enum <= 2) then
									for Idx = Inst[2], Inst[3] do
										Stk[Idx] = nil;
									end
								elseif (Enum > 3) then
									if Stk[Inst[2]] then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								else
									Upvalues[Inst[3]] = Stk[Inst[2]];
								end
							elseif (Enum <= 7) then
								if (Enum <= 5) then
									Stk[Inst[2]][Inst[3]] = Inst[4];
								elseif (Enum > 6) then
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								else
									local A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								end
							elseif (Enum <= 8) then
								if not Stk[Inst[2]] then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							elseif (Enum > 9) then
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							else
								Stk[Inst[2]] = Stk[Inst[3]];
							end
						elseif (Enum <= 16) then
							if (Enum <= 13) then
								if (Enum <= 11) then
									Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
								elseif (Enum > 12) then
									local A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
								else
									Stk[Inst[2]] = Stk[Inst[3]];
								end
							elseif (Enum <= 14) then
								local A = Inst[2];
								local Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Top)));
								Top = (Limit + A) - 1;
								local Edx = 0;
								for Idx = A, Top do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
							elseif (Enum == 15) then
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							else
								local A = Inst[2];
								local B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
							end
						elseif (Enum <= 19) then
							if (Enum <= 17) then
								local A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
							elseif (Enum == 18) then
								local A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
							else
								local A = Inst[2];
								do
									return Stk[A](Unpack(Stk, A + 1, Inst[3]));
								end
							end
						elseif (Enum <= 20) then
							do
								return;
							end
						elseif (Enum > 21) then
							do
								return Stk[Inst[2]]();
							end
						else
							Stk[Inst[2]] = Env[Inst[3]];
						end
					elseif (Enum <= 34) then
						if (Enum <= 28) then
							if (Enum <= 25) then
								if (Enum <= 23) then
									Stk[Inst[2]] = Stk[Inst[3]] % Stk[Inst[4]];
								elseif (Enum == 24) then
									Stk[Inst[2]] = Inst[3] ~= 0;
								else
									Stk[Inst[2]] = Inst[3] + Stk[Inst[4]];
								end
							elseif (Enum <= 26) then
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							elseif (Enum > 27) then
								Stk[Inst[2]] = #Stk[Inst[3]];
							else
								do
									return Stk[Inst[2]];
								end
							end
						elseif (Enum <= 31) then
							if (Enum <= 29) then
								Upvalues[Inst[3]] = Stk[Inst[2]];
							elseif (Enum == 30) then
								do
									return Stk[Inst[2]]();
								end
							else
								Stk[Inst[2]] = Env[Inst[3]];
							end
						elseif (Enum <= 32) then
							Stk[Inst[2]] = Inst[3] + Stk[Inst[4]];
						elseif (Enum == 33) then
							local A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
						else
							Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
						end
					elseif (Enum <= 40) then
						if (Enum <= 37) then
							if (Enum <= 35) then
								local A = Inst[2];
								do
									return Stk[A](Unpack(Stk, A + 1, Top));
								end
							elseif (Enum > 36) then
								local A = Inst[2];
								local Results = {Stk[A](Stk[A + 1])};
								local Edx = 0;
								for Idx = A, Inst[4] do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
							else
								VIP = Inst[3];
							end
						elseif (Enum <= 38) then
							if (Inst[2] == Stk[Inst[4]]) then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						elseif (Enum == 39) then
							if not Stk[Inst[2]] then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
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
								if (Mvm[1] == 9) then
									Indexes[Idx - 1] = {Stk,Mvm[3]};
								else
									Indexes[Idx - 1] = {Upvalues,Mvm[3]};
								end
								Lupvals[#Lupvals + 1] = Indexes;
							end
							Stk[Inst[2]] = Wrap(NewProto, NewUvals, Env);
						end
					elseif (Enum <= 43) then
						if (Enum <= 41) then
							Stk[Inst[2]] = #Stk[Inst[3]];
						elseif (Enum == 42) then
							if (Stk[Inst[2]] < Stk[Inst[4]]) then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						elseif (Inst[2] == Stk[Inst[4]]) then
							VIP = VIP + 1;
						else
							VIP = Inst[3];
						end
					elseif (Enum <= 44) then
						local A = Inst[2];
						local Results, Limit = _R(Stk[A](Stk[A + 1]));
						Top = (Limit + A) - 1;
						local Edx = 0;
						for Idx = A, Top do
							Edx = Edx + 1;
							Stk[Idx] = Results[Edx];
						end
					elseif (Enum == 45) then
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
						local B = Stk[Inst[3]];
						Stk[A + 1] = B;
						Stk[A] = B[Inst[4]];
					end
				elseif (Enum <= 70) then
					if (Enum <= 58) then
						if (Enum <= 52) then
							if (Enum <= 49) then
								if (Enum <= 47) then
									local A = Inst[2];
									Stk[A] = Stk[A](Stk[A + 1]);
								elseif (Enum == 48) then
									local A = Inst[2];
									Stk[A] = Stk[A]();
								else
									Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
								end
							elseif (Enum <= 50) then
								for Idx = Inst[2], Inst[3] do
									Stk[Idx] = nil;
								end
							elseif (Enum == 51) then
								do
									return Stk[Inst[2]];
								end
							else
								local A = Inst[2];
								do
									return Stk[A](Unpack(Stk, A + 1, Top));
								end
							end
						elseif (Enum <= 55) then
							if (Enum <= 53) then
								local A = Inst[2];
								do
									return Unpack(Stk, A, A + Inst[3]);
								end
							elseif (Enum > 54) then
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
								local Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
								Top = (Limit + A) - 1;
								local Edx = 0;
								for Idx = A, Top do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
							end
						elseif (Enum <= 56) then
							Stk[Inst[2]] = Upvalues[Inst[3]];
						elseif (Enum == 57) then
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
							do
								return Unpack(Stk, A, Top);
							end
						end
					elseif (Enum <= 64) then
						if (Enum <= 61) then
							if (Enum <= 59) then
								local A = Inst[2];
								do
									return Unpack(Stk, A, Top);
								end
							elseif (Enum > 60) then
								Stk[Inst[2]][Inst[3]] = Inst[4];
							elseif (Stk[Inst[2]] ~= Stk[Inst[4]]) then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						elseif (Enum <= 62) then
							Stk[Inst[2]] = Inst[3] ~= 0;
						elseif (Enum > 63) then
							if (Stk[Inst[2]] == Stk[Inst[4]]) then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
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
								if (Mvm[1] == 9) then
									Indexes[Idx - 1] = {Stk,Mvm[3]};
								else
									Indexes[Idx - 1] = {Upvalues,Mvm[3]};
								end
								Lupvals[#Lupvals + 1] = Indexes;
							end
							Stk[Inst[2]] = Wrap(NewProto, NewUvals, Env);
						end
					elseif (Enum <= 67) then
						if (Enum <= 65) then
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
						elseif (Enum > 66) then
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
							local Results = {Stk[A](Stk[A + 1])};
							local Edx = 0;
							for Idx = A, Inst[4] do
								Edx = Edx + 1;
								Stk[Idx] = Results[Edx];
							end
						end
					elseif (Enum <= 68) then
						local A = Inst[2];
						Stk[A] = Stk[A]();
					elseif (Enum > 69) then
						Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
					else
						Stk[Inst[2]] = {};
					end
				elseif (Enum <= 82) then
					if (Enum <= 76) then
						if (Enum <= 73) then
							if (Enum <= 71) then
								Stk[Inst[2]] = Stk[Inst[3]] % Stk[Inst[4]];
							elseif (Enum > 72) then
								if (Stk[Inst[2]] == Inst[4]) then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							elseif (Stk[Inst[2]] < Stk[Inst[4]]) then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						elseif (Enum <= 74) then
							if (Stk[Inst[2]] == Stk[Inst[4]]) then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						elseif (Enum == 75) then
							local A = Inst[2];
							Stk[A] = Stk[A](Stk[A + 1]);
						else
							do
								return;
							end
						end
					elseif (Enum <= 79) then
						if (Enum <= 77) then
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
						elseif (Enum == 78) then
							local A = Inst[2];
							do
								return Stk[A](Unpack(Stk, A + 1, Inst[3]));
							end
						elseif Stk[Inst[2]] then
							VIP = VIP + 1;
						else
							VIP = Inst[3];
						end
					elseif (Enum <= 80) then
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
					elseif (Enum > 81) then
						if (Stk[Inst[2]] == Inst[4]) then
							VIP = VIP + 1;
						else
							VIP = Inst[3];
						end
					else
						Stk[Inst[2]]();
					end
				elseif (Enum <= 88) then
					if (Enum <= 85) then
						if (Enum <= 83) then
							VIP = Inst[3];
						elseif (Enum == 84) then
							Stk[Inst[2]] = Inst[3];
						else
							Stk[Inst[2]] = Stk[Inst[3]] % Inst[4];
						end
					elseif (Enum <= 86) then
						Stk[Inst[2]] = {};
					elseif (Enum == 87) then
						local A = Inst[2];
						Stk[A](Unpack(Stk, A + 1, Top));
					else
						Stk[Inst[2]] = Upvalues[Inst[3]];
					end
				elseif (Enum <= 91) then
					if (Enum <= 89) then
						if (Stk[Inst[2]] ~= Stk[Inst[4]]) then
							VIP = VIP + 1;
						else
							VIP = Inst[3];
						end
					elseif (Enum > 90) then
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
						Stk[Inst[2]] = Inst[3];
					end
				elseif (Enum <= 92) then
					local A = Inst[2];
					Stk[A](Unpack(Stk, A + 1, Top));
				elseif (Enum == 93) then
					local A = Inst[2];
					local Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
					Top = (Limit + A) - 1;
					local Edx = 0;
					for Idx = A, Top do
						Edx = Edx + 1;
						Stk[Idx] = Results[Edx];
					end
				else
					Stk[Inst[2]]();
				end
				VIP = VIP + 1;
			end
		end;
	end
	return Wrap(Deserialize(), {}, vmenv)(...);
end
return VMCall("LOL!153Q0003063Q00737472696E6703043Q006368617203043Q00627974652Q033Q0073756203053Q0062697433322Q033Q0062697403043Q0062786F7203053Q007461626C6503063Q00636F6E63617403063Q00696E7365727403043Q0067616D65030A3Q0047657453657276696365030B3Q006A14E73B7A4712E5224A4703053Q00292260934B03073Q007072656D69756D010003753Q00DF1E163ACA58F58CC50B1564DE0BAECBC2081739DC10B9CCD91E0724CD4CB9CCDA452732C90EB5D1D22E073CDC0EB5D3DA0F0C3EEA1BA9D7D2071165F51BA8C29818072CCA4DB2C6D60E1165D403B3CD98200500EC2F82F9E72B1265F20CE3D0D80D077AFC2FF59AFD590878CA54EECEFC440E3FD803083Q00A3B76A624AB962DA030A3Q00496E697469616C697A65030C3Q0041757468656E74696361746503103Q004175746F41757468656E746963617465003A3Q00121F3Q00013Q00200F5Q000200121F000100013Q00200F00010001000300121F000200013Q00200F00020002000400121F000300053Q0006080003000A000100010004243Q000A000100121F000300063Q00200F00040003000700121F000500083Q00200F00050005000900121F000600083Q00200F00060006000A00062800073Q000100062Q00093Q00064Q00098Q00093Q00044Q00093Q00014Q00093Q00024Q00093Q00053Q00121F0008000B3Q00202E00080008000C2Q000C000A00073Q00125A000B000D3Q00125A000C000E4Q0036000A000C4Q000D00083Q00022Q005600096Q0018000A5Q00303D0009000F00102Q000C000B00073Q00125A000C00113Q00125A000D00124Q0006000B000D0002000628000C0001000100022Q00093Q000B4Q00093Q00073Q000628000D0002000100022Q00093Q000A4Q00093Q00073Q000628000E0003000100022Q00093Q00074Q00093Q000A3Q00101A00090013000E000628000E0004000100032Q00093Q00074Q00093Q000D4Q00093Q000C3Q00101A00090014000E000628000E0005000100032Q00093Q000D4Q00093Q00094Q00093Q00073Q00101A00090015000E2Q001B000900024Q00143Q00013Q00063Q00023Q00026Q00F03F026Q00704002264Q005600025Q00125A000300014Q002900045Q00125A000500013Q0004500003002100012Q005800076Q000C000800024Q0058000900014Q0058000A00024Q0058000B00034Q0058000C00044Q000C000D6Q000C000E00063Q002022000F000600012Q0036000C000F4Q000D000B3Q00022Q0058000C00034Q0058000D00044Q000C000E00014Q0029000F00014Q0047000F0006000F001020000F0001000F2Q0029001000014Q00470010000600100010200010000100100020220010001000012Q0036000D00104Q0043000C6Q000D000A3Q0002002055000A000A00022Q002C0009000A4Q005C00073Q000100044D0003000500012Q0058000300054Q000C000400024Q0013000300044Q003B00036Q00143Q00017Q00073Q00028Q0003053Q007063612Q6C03053Q007072696E74032A3Q002286D22E26CDDB2E0A978B0F32E5DD320AB9CD292BEAC7771FAFDF3F2FE3DA7712AFD22F67E2DF2318E403083Q005779CAAB5C4786BE03223Q0012E43E9A26D311C80FC025842CC56C9C26812A8D3DC224C822C4359B69C52D9C289B03043Q00E849A14C00283Q00125A3Q00014Q0002000100023Q0026493Q0002000100010004243Q0002000100121F000300023Q00062800043Q000100012Q00388Q00420003000200042Q000C000200044Q000C000100033Q00064F0001001800013Q0004243Q0018000100125A000300013Q0026490003000D000100010004243Q000D000100121F000400034Q0058000500013Q00125A000600043Q00125A000700054Q0036000500074Q005C00043Q00012Q001B000200023Q0004243Q000D00010004243Q0027000100125A000300013Q00264900030019000100010004243Q0019000100121F000400034Q0058000500013Q00125A000600063Q00125A000700074Q00060005000700022Q000C000600024Q00110004000600012Q0002000400044Q001B000400023Q0004243Q001900010004243Q002700010004243Q000200012Q00143Q00013Q00013Q00033Q00030A3Q006C6F6164737472696E6703043Q0067616D6503073Q00482Q747047657400093Q00121F3Q00013Q00121F000100023Q00202E0001000100032Q005800036Q0036000100034Q000D5Q00022Q00163Q00014Q003B8Q00143Q00017Q00033Q0003053Q00652Q726F72036C3Q0080F55B4F1F90DC5B4E23FBEC4C5C0BAFD14D4F17A1DC461D1FB8DA474E0DF5996F521AAED5471D18AED7414917B4D7435117AFC0025111B8D2475950FBE94E581FA8DC025C0BAFD147530AB2DA43491BFBCC515410BC9956551BFBDA4D4F0CBEDA561D0BA8DC025E11BFDC0C03053Q007EDBB9223D000A4Q00587Q0006083Q0009000100010004243Q0009000100121F3Q00014Q0058000100013Q00125A000200023Q00125A000300034Q0036000100034Q005C5Q00012Q00143Q00017Q00093Q00028Q0003113Q0029F66E575D43D6C333FB6D574154DCC32903083Q00876CAE3E121E179303053Q007072696E7403403Q008DC533D9198536DEA5D46AF80DAD30C2A5FA2CDE14A22A87B7FC3EC31DA027CEB5E83ECE1CEE24CEA2E16ADF10AB73C4B9FB38CE1BBA73D2A5EC6AC817AA368903083Q00A7D6894AAB78CE5303053Q00652Q726F7203253Q00B0DC2B4FF98C8EE92160B88E85E63351F1A3CBE52158B8A484F4371DE8B584E63B59FDA3C503063Q00C7EB90523D9802223Q00125A000200014Q0002000300033Q00264900020002000100010004243Q000200012Q005800045Q00125A000500023Q00125A000600034Q00060004000600022Q000C000300043Q00064000010019000100030004243Q0019000100125A000400013Q0026490004000C000100010004243Q000C00012Q0018000500014Q001D000500013Q00121F000500044Q005800065Q00125A000700053Q00125A000800064Q0036000600084Q005C00053Q00010004243Q002100010004243Q000C00010004243Q0021000100121F000400074Q005800055Q00125A000600083Q00125A000700094Q0036000500074Q005C00043Q00010004243Q002100010004243Q000200012Q00143Q00017Q00273Q00028Q00027Q004003053Q007063612Q6C03053Q007072696E74031B3Q00FC786906B835C24D6329F938C240731CBC1A87616311AB5EEE642A03063Q007EA7341074D903203Q00F30B3292BB0BC188082189B81CF8883A2FC0B21CE8CB2660B5A71CEE880710DA03073Q009CA84E40E0D47903183Q0032E0A4CC0BEBE5DA08AEA3CB13EDAD8E12FDA0DC47C7958003043Q00AE678EC5026Q000840031E3Q006D04462A2475FD4F3B6278044BEC5E2D512Q2C5DF94221513F6555FD4F7203073Q009836483F58453E026Q00F03F026Q001040030E3Q00FFC1F71CDACBFA1CD2CBFB52D08A03043Q003CB4A48E03153Q006D50042Q2BE8524C51452F22F911501E0E2C3EFE5C03073Q0072383E6549478D03053Q0070616972732Q033Q004B6579030C3Q0093ECC284BDF1CBCDAAECDF8A03043Q00A4D889BB03023Q004950036A3Q00E6EE38A1E6F50ECBA638A1E6FF08C6EF27B7EABE09C7F271BCA9EA4BC2E738A0A3FA4BC6E971ABA9EB4592CF37F2B2F602C1A638A1E6FF4BD6E327BBA5FB4BD1EE30BCA1FB4792E53EBCB2FF08C6A622A7B6EE04C0F271A6A9BE19D7F630BBB4BE12DDF323F2ADFB129C03073Q006BB28651D2C69E03023Q006F7303043Q0074696D6503043Q00210B83D403053Q00CA586EE2A6030A3Q004578706972655965617203053Q00CE008CE3C203053Q00AAA36FE297030B3Q004578706972654D6F6E74682Q033Q001531AB03073Q00497150D2582E5703093Q00457870697265446179031B3Q00AA29D452F18020C416E69529C952F4942FCE17F4922AD81EEB986D03053Q0087E14CAD72029A3Q00125A000200014Q0002000300063Q000E260002002C000100020004243Q002C000100121F000700033Q00062800083Q000100012Q00388Q00420007000200082Q000C000600084Q000C000500073Q00064F0005001A00013Q0004243Q001A000100125A000700013Q0026490007000D000100010004243Q000D00012Q000C000400063Q00121F000800044Q005800095Q00125A000A00053Q00125A000B00064Q00060009000B00022Q000C000A00044Q00110008000A00010004243Q002B00010004243Q000D00010004243Q002B000100125A000700013Q0026490007001B000100010004243Q001B000100121F000800044Q005800095Q00125A000A00073Q00125A000B00084Q00060009000B00022Q000C000A00064Q00110008000A00012Q001800086Q005800095Q00125A000A00093Q00125A000B000A4Q00360009000B4Q003B00085Q0004243Q001B000100125A0002000B3Q000E2600010038000100020004243Q003800012Q0058000700014Q005100070001000100121F000700044Q005800085Q00125A0009000C3Q00125A000A000D4Q00060008000A00022Q000C000900014Q001100070009000100125A0002000E3Q002649000200400001000F0004243Q004000012Q001800076Q005800085Q00125A000900103Q00125A000A00114Q00360008000A4Q003B00075Q002649000200470001000E0004243Q004700012Q0058000700024Q00440007000100022Q000C000300074Q0002000400043Q00125A000200023Q002649000200020001000B0004243Q0002000100060800030051000100010004243Q005100012Q001800076Q005800085Q00125A000900123Q00125A000A00134Q00360008000A4Q003B00075Q00121F000700144Q000C000800034Q00420007000200090004243Q0095000100200F000C000B0015000640000C0095000100010004243Q0095000100125A000C00014Q0002000D000E3Q002649000C006E0001000E0004243Q006E000100062A000E00640001000D0004243Q006400012Q0018000F6Q005800105Q00125A001100163Q00125A001200174Q0036001000124Q003B000F5Q00200F000F000B001800063C000F006D000100040004243Q006D00012Q0018000F6Q005800105Q00125A001100193Q00125A0012001A4Q0036001000124Q003B000F5Q00125A000C00023Q000E260001008C0001000C0004243Q008C000100121F000F001B3Q00200F000F000F001C2Q0044000F000100022Q000C000D000F3Q00121F000F001B3Q00200F000F000F001C2Q005600103Q00032Q005800115Q00125A0012001D3Q00125A0013001E4Q000600110013000200200F0012000B001F2Q00310010001100122Q005800115Q00125A001200203Q00125A001300214Q000600110013000200200F0012000B00222Q00310010001100122Q005800115Q00125A001200233Q00125A001300244Q000600110013000200200F0012000B00252Q00310010001100122Q002F000F000200022Q000C000E000F3Q00125A000C000E3Q002649000C005A000100020004243Q005A00012Q0018000F00014Q005800105Q00125A001100263Q00125A001200274Q0036001000124Q003B000F5Q0004243Q005A000100064100070055000100020004243Q0055000100125A0002000F3Q0004243Q000200012Q00143Q00013Q00013Q00043Q0003043Q0067616D6503073Q00482Q747047657403153Q000F02AD3B144CF6642Q06B0650E06B02D1E58B6390003043Q004B6776D900093Q00121F3Q00013Q00202E5Q00022Q005800025Q00125A000300033Q00125A000400044Q0036000200044Q00348Q003B8Q00143Q00017Q000B3Q00028Q0003073Q007072656D69756D03053Q007072696E7403393Q0021C1A1A2AD96A203FE85F082B2A957FDAAB5A1B4B217ADB5BFA8B8FD5AFEB3B9BCADAE14EAF8BBA9A4E71BF8ACB8A92QB313EEB9A4A5B2A95403073Q00C77A8DD8D0CCDD026Q00F03F032F3Q0096F109E279DDA8C403CD38D8A29D03F16EF3A99D1BF561B6ABD205FE7CB6ABD202B068E4A8D019E575B6A0D214F53603063Q0096CDBD70901803383Q000B8BFF5F059E2Q14658FBA55448E1E052B80F10C349A141D2C91B20C09872Q156596BA5D1181031536C4BE42448912042C92BA0C0F8D085E03083Q007045E4DF2C64E871030C3Q0041757468656E74696361746502303Q00125A000200013Q00264900020016000100010004243Q001600012Q005800036Q00510003000100012Q0058000300013Q00200F00030003000200060800030015000100010004243Q0015000100125A000300013Q0026490003000A000100010004243Q000A000100121F000400034Q0058000500023Q00125A000600043Q00125A000700054Q0036000500074Q005C00043Q00012Q0018000400014Q001B000400023Q0004243Q000A000100125A000200063Q00264900020001000100060004243Q000100010006080001002A000100010004243Q002A000100125A000300013Q0026490003001B000100010004243Q001B000100121F000400034Q0058000500023Q00125A000600073Q00125A000700084Q0036000500074Q005C00043Q00012Q001800046Q0058000500023Q00125A000600093Q00125A0007000A4Q0036000500074Q003B00045Q0004243Q001B000100202E00033Q000B2Q000C000500014Q0013000300054Q003B00035Q0004243Q000100012Q00143Q00017Q00", GetFEnv(), ...);
