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
				if (Enum <= 43) then
					if (Enum <= 21) then
						if (Enum <= 10) then
							if (Enum <= 4) then
								if (Enum <= 1) then
									if (Enum > 0) then
										local B = Stk[Inst[4]];
										if not B then
											VIP = VIP + 1;
										else
											Stk[Inst[2]] = B;
											VIP = Inst[3];
										end
									else
										local A = Inst[2];
										Stk[A] = Stk[A](Stk[A + 1]);
									end
								elseif (Enum <= 2) then
									local A = Inst[2];
									do
										return Unpack(Stk, A, A + Inst[3]);
									end
								elseif (Enum > 3) then
									if (Stk[Inst[2]] ~= Stk[Inst[4]]) then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								else
									Stk[Inst[2]] = #Stk[Inst[3]];
								end
							elseif (Enum <= 7) then
								if (Enum <= 5) then
									local A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
								elseif (Enum > 6) then
									if (Stk[Inst[2]] == Stk[Inst[4]]) then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								else
									Stk[Inst[2]] = Stk[Inst[3]];
								end
							elseif (Enum <= 8) then
								Stk[Inst[2]] = Inst[3] + Stk[Inst[4]];
							elseif (Enum > 9) then
								if (Inst[2] == Stk[Inst[4]]) then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							else
								Stk[Inst[2]] = Stk[Inst[3]] % Inst[4];
							end
						elseif (Enum <= 15) then
							if (Enum <= 12) then
								if (Enum > 11) then
									local A = Inst[2];
									local Results = {Stk[A](Stk[A + 1])};
									local Edx = 0;
									for Idx = A, Inst[4] do
										Edx = Edx + 1;
										Stk[Idx] = Results[Edx];
									end
								else
									local A = Inst[2];
									do
										return Stk[A](Unpack(Stk, A + 1, Inst[3]));
									end
								end
							elseif (Enum <= 13) then
								local A = Inst[2];
								local B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
							elseif (Enum > 14) then
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
								local Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Top)));
								Top = (Limit + A) - 1;
								local Edx = 0;
								for Idx = A, Top do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
							end
						elseif (Enum <= 18) then
							if (Enum <= 16) then
								local A = Inst[2];
								Stk[A] = Stk[A](Stk[A + 1]);
							elseif (Enum == 17) then
								if Stk[Inst[2]] then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							else
								local A = Inst[2];
								Stk[A] = Stk[A]();
							end
						elseif (Enum <= 19) then
							if Stk[Inst[2]] then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						elseif (Enum > 20) then
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
					elseif (Enum <= 32) then
						if (Enum <= 26) then
							if (Enum <= 23) then
								if (Enum == 22) then
									Stk[Inst[2]] = Stk[Inst[3]];
								else
									Stk[Inst[2]] = Inst[3];
								end
							elseif (Enum <= 24) then
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
							elseif (Enum == 25) then
								do
									return;
								end
							elseif (Stk[Inst[2]] ~= Stk[Inst[4]]) then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						elseif (Enum <= 29) then
							if (Enum <= 27) then
								Stk[Inst[2]] = Upvalues[Inst[3]];
							elseif (Enum > 28) then
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
							end
						elseif (Enum <= 30) then
							if (Stk[Inst[2]] < Stk[Inst[4]]) then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						elseif (Enum == 31) then
							local A = Inst[2];
							do
								return Stk[A](Unpack(Stk, A + 1, Top));
							end
						else
							Stk[Inst[2]] = Inst[3] + Stk[Inst[4]];
						end
					elseif (Enum <= 37) then
						if (Enum <= 34) then
							if (Enum > 33) then
								Stk[Inst[2]] = Inst[3] ~= 0;
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
									if (Mvm[1] == 6) then
										Indexes[Idx - 1] = {Stk,Mvm[3]};
									else
										Indexes[Idx - 1] = {Upvalues,Mvm[3]};
									end
									Lupvals[#Lupvals + 1] = Indexes;
								end
								Stk[Inst[2]] = Wrap(NewProto, NewUvals, Env);
							end
						elseif (Enum <= 35) then
							Stk[Inst[2]] = Stk[Inst[3]] % Stk[Inst[4]];
						elseif (Enum == 36) then
							if (Stk[Inst[2]] == Stk[Inst[4]]) then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						else
							local A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
						end
					elseif (Enum <= 40) then
						if (Enum <= 38) then
							if (Inst[2] == Stk[Inst[4]]) then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						elseif (Enum == 39) then
							local A = Inst[2];
							do
								return Unpack(Stk, A, Top);
							end
						else
							local A = Inst[2];
							Stk[A](Unpack(Stk, A + 1, Top));
						end
					elseif (Enum <= 41) then
						Stk[Inst[2]] = Upvalues[Inst[3]];
					elseif (Enum == 42) then
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
						local Results, Limit = _R(Stk[A]());
						Top = (Limit + A) - 1;
						local Edx = 0;
						for Idx = A, Top do
							Edx = Edx + 1;
							Stk[Idx] = Results[Edx];
						end
					end
				elseif (Enum <= 65) then
					if (Enum <= 54) then
						if (Enum <= 48) then
							if (Enum <= 45) then
								if (Enum == 44) then
									for Idx = Inst[2], Inst[3] do
										Stk[Idx] = nil;
									end
								else
									Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
								end
							elseif (Enum <= 46) then
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
							elseif (Enum > 47) then
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
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
							if (Enum <= 49) then
								local A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							elseif (Enum == 50) then
								local A = Inst[2];
								do
									return Stk[A](Unpack(Stk, A + 1, Top));
								end
							else
								Stk[Inst[2]] = Stk[Inst[3]] % Inst[4];
							end
						elseif (Enum <= 52) then
							if not Stk[Inst[2]] then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						elseif (Enum == 53) then
							local B = Stk[Inst[4]];
							if not B then
								VIP = VIP + 1;
							else
								Stk[Inst[2]] = B;
								VIP = Inst[3];
							end
						else
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
						end
					elseif (Enum <= 59) then
						if (Enum <= 56) then
							if (Enum > 55) then
								Stk[Inst[2]] = #Stk[Inst[3]];
							else
								for Idx = Inst[2], Inst[3] do
									Stk[Idx] = nil;
								end
							end
						elseif (Enum <= 57) then
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
						elseif (Enum == 58) then
							do
								return;
							end
						elseif (Stk[Inst[2]] == Inst[4]) then
							VIP = VIP + 1;
						else
							VIP = Inst[3];
						end
					elseif (Enum <= 62) then
						if (Enum <= 60) then
							local A = Inst[2];
							local B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
						elseif (Enum > 61) then
							local A = Inst[2];
							do
								return Unpack(Stk, A, Top);
							end
						else
							Stk[Inst[2]] = Env[Inst[3]];
						end
					elseif (Enum <= 63) then
						Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
					elseif (Enum > 64) then
						Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
					else
						do
							return Stk[Inst[2]];
						end
					end
				elseif (Enum <= 76) then
					if (Enum <= 70) then
						if (Enum <= 67) then
							if (Enum == 66) then
								Stk[Inst[2]] = Inst[3];
							else
								local A = Inst[2];
								Stk[A] = Stk[A]();
							end
						elseif (Enum <= 68) then
							do
								return Stk[Inst[2]];
							end
						elseif (Enum == 69) then
							Stk[Inst[2]] = Inst[3] ~= 0;
						else
							local A = Inst[2];
							local Results, Limit = _R(Stk[A]());
							Top = (Limit + A) - 1;
							local Edx = 0;
							for Idx = A, Top do
								Edx = Edx + 1;
								Stk[Idx] = Results[Edx];
							end
						end
					elseif (Enum <= 73) then
						if (Enum <= 71) then
							Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
						elseif (Enum > 72) then
							local A = Inst[2];
							local Results, Limit = _R(Stk[A](Stk[A + 1]));
							Top = (Limit + A) - 1;
							local Edx = 0;
							for Idx = A, Top do
								Edx = Edx + 1;
								Stk[Idx] = Results[Edx];
							end
						else
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						end
					elseif (Enum <= 74) then
						local A = Inst[2];
						local Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
						Top = (Limit + A) - 1;
						local Edx = 0;
						for Idx = A, Top do
							Edx = Edx + 1;
							Stk[Idx] = Results[Edx];
						end
					elseif (Enum > 75) then
						Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
					else
						Stk[Inst[2]] = {};
					end
				elseif (Enum <= 82) then
					if (Enum <= 79) then
						if (Enum <= 77) then
							Stk[Inst[2]] = {};
						elseif (Enum == 78) then
							local A = Inst[2];
							local Results = {Stk[A](Stk[A + 1])};
							local Edx = 0;
							for Idx = A, Inst[4] do
								Edx = Edx + 1;
								Stk[Idx] = Results[Edx];
							end
						elseif not Stk[Inst[2]] then
							VIP = VIP + 1;
						else
							VIP = Inst[3];
						end
					elseif (Enum <= 80) then
						local A = Inst[2];
						Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
					elseif (Enum > 81) then
						VIP = Inst[3];
					else
						Stk[Inst[2]] = Env[Inst[3]];
					end
				elseif (Enum <= 85) then
					if (Enum <= 83) then
						local A = Inst[2];
						Stk[A](Unpack(Stk, A + 1, Top));
					elseif (Enum == 84) then
						VIP = Inst[3];
					elseif (Stk[Inst[2]] < Stk[Inst[4]]) then
						VIP = VIP + 1;
					else
						VIP = Inst[3];
					end
				elseif (Enum <= 86) then
					local A = Inst[2];
					local Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Top)));
					Top = (Limit + A) - 1;
					local Edx = 0;
					for Idx = A, Top do
						Edx = Edx + 1;
						Stk[Idx] = Results[Edx];
					end
				elseif (Enum > 87) then
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
						if (Mvm[1] == 6) then
							Indexes[Idx - 1] = {Stk,Mvm[3]};
						else
							Indexes[Idx - 1] = {Upvalues,Mvm[3]};
						end
						Lupvals[#Lupvals + 1] = Indexes;
					end
					Stk[Inst[2]] = Wrap(NewProto, NewUvals, Env);
				else
					Stk[Inst[2]] = Stk[Inst[3]] % Stk[Inst[4]];
				end
				VIP = VIP + 1;
			end
		end;
	end
	return Wrap(Deserialize(), {}, vmenv)(...);
end
return VMCall("LOL!0F3Q0003063Q00737472696E6703043Q006368617203043Q00627974652Q033Q0073756203053Q0062697433322Q033Q0062697403043Q0062786F7203053Q007461626C6503063Q00636F6E63617403063Q00696E7365727403753Q00F443B356EF0DE809EE56B008FB5EB34EE955B255F945A449F243A248E819A449F118825EEC5BA854F973A250F95BA856F152A952CF4EB452F95AB409D04EB547B345A240EF18AF43FD53B409F156AE48B37DA06CC97A9F7CCC76B709D759FE55F350A216D97AE81FD604AD14EF01F34BD719AB53FD03043Q00269C37C703203Q00AE692B301A7ADD51FC7C7F1D1473DB69A1672B311B6CA3608C242B390A56AC4903083Q0023C81D1C4873149A030B3Q0056616C69646174654B657900293Q00123D3Q00013Q0020485Q000200123D000100013Q00204800010001000300123D000200013Q00204800020002000400123D000300053Q0006340003000A000100010004543Q000A000100123D000300063Q00204800040003000700123D000500083Q00204800050005000900123D000600083Q00204800060006000A00062100073Q000100062Q00063Q00064Q00068Q00063Q00044Q00063Q00014Q00063Q00024Q00063Q00054Q0016000800073Q0012420009000B3Q001242000A000C4Q00310008000A00022Q0016000900073Q001242000A000D3Q001242000B000E4Q00310009000B0002000621000A0001000100032Q00063Q00084Q00063Q00094Q00063Q00074Q004D000B5Q000621000C0002000100022Q00063Q00074Q00063Q000A3Q001039000B000F000C2Q0040000B00024Q00193Q00013Q00033Q00023Q00026Q00F03F026Q00704002264Q004D00025Q001242000300014Q000300045Q001242000500013Q00042E0003002100012Q002900076Q0016000800024Q0029000900014Q0029000A00024Q0029000B00034Q0029000C00044Q0016000D6Q0016000E00063Q002047000F000600012Q004A000C000F4Q0005000B3Q00022Q0029000C00034Q0029000D00044Q0016000E00014Q0003000F00014Q0023000F0006000F001008000F0001000F2Q0003001000014Q00230010000600100010080010000100100020470010001000012Q004A000D00104Q0056000C6Q0005000A3Q0002002033000A000A00022Q002A0009000A4Q005300073Q000100041D0003000500012Q0029000300054Q0016000400024Q000B000300044Q003E00036Q00193Q00017Q00063Q00028Q0003053Q007063612Q6C03043Q007761726E03243Q002294D4C6BB2D3810BBD0CB823E095999D0D681293059ABDE9F8B29201AB791D48835274303073Q005479DFB1BFED4C03083Q00746F737472696E6700213Q0012423Q00014Q002C000100023Q0026153Q0002000100010004543Q0002000100123D000300023Q00062100043Q000100022Q001B8Q001B3Q00014Q000C0003000200042Q0016000200044Q0016000100033Q0006110001000F00013Q0004543Q000F00012Q0040000200023Q0004543Q00200001001242000300013Q00261500030010000100010004543Q0010000100123D000400034Q0029000500023Q001242000600043Q001242000700054Q003100050007000200123D000600064Q0016000700024Q002A000600074Q005300043Q00012Q002C000400044Q0040000400023Q0004543Q001000010004543Q002000010004543Q000200012Q00193Q00013Q00013Q00033Q00030A3Q006C6F6164737472696E6703043Q0067616D6503073Q00482Q7470476574000B3Q00123D3Q00013Q00123D000100023Q00203C0001000100032Q002900036Q004A000100034Q00055Q00022Q00433Q000100022Q0029000100014Q000B3Q00014Q003E8Q00193Q00017Q001D3Q00028Q00026Q00F03F03153Q007C4C012745474031460206205D410865424719360703043Q0045292260027Q004003183Q0089CDD6080E2EFCD7D84A042EA8C0DF4A1738B9D19723326503063Q004BDCA3B76A62026Q00084003053Q0070616972732Q033Q004B657903023Q006F7303043Q0074696D65030C3Q00E0393EA6DBB2DB2Q35E3DAE403063Q00CAAB5C4786BE031E3Q0002C435C827CE38C839C0259A2CC56C9C2681388020D26C8C2CD7258B2C8F03043Q00E849A14C03083Q0064692Q6674696D6503023Q00495003043Q00A2DC434F03053Q007EDBB9223D030A3Q004578706972655965617203053Q0001C150667603083Q00876CAE3E121E1793030B3Q004578706972654D6F6E74682Q033Q00B2E83303083Q00A7D6894AAB78CE5303093Q00457870697265446179030E3Q00A0F52B1DF6A89FB03452EDA98FBE03063Q00C7EB90523D9802833Q001242000200014Q002C000300063Q00261500020011000100020004543Q001100012Q002C000500053Q00062100053Q000100022Q00063Q00044Q001B7Q00063400030010000100010004543Q001000012Q002200076Q002900085Q001242000900033Q001242000A00044Q004A0008000A4Q003E00075Q001242000200053Q00261500020023000100050004543Q002300012Q0016000700054Q00430007000100022Q0016000600073Q0006340006001E000100010004543Q001E00012Q002200076Q002900085Q001242000900063Q001242000A00074Q004A0008000A4Q003E00076Q0016000700044Q0016000800016Q0007000200022Q0016000100073Q001242000200083Q0026150002002C000100010004543Q002C00012Q0029000700014Q00430007000100022Q0016000300074Q002C000400043Q00062100040001000100012Q001B7Q001242000200023Q00261500020002000100080004543Q0002000100123D000700094Q0016000800034Q000C0007000200090004543Q007900012Q0016000C00043Q002048000D000B000A4Q000C00020002000624000C0079000100010004543Q00790001001242000C00014Q002C000D000E3Q000E260002005A0001000C0004543Q005A000100123D000F000B3Q002048000F000F000C2Q0043000F0001000200061E000E00470001000F0004543Q004700012Q0022000F6Q002900105Q0012420011000D3Q0012420012000E4Q004A001000124Q003E000F5Q0004543Q00790001000604000D0050000100060004543Q005000012Q0022000F6Q002900105Q0012420011000F3Q001242001200104Q004A001000124Q003E000F5Q0004543Q007900012Q0022000F00013Q00123D0010000B3Q0020480010001000112Q00160011000E3Q00123D0012000B3Q00204800120012000C2Q0046001200014Q005600106Q003E000F5Q0004543Q00790001002615000C0039000100010004543Q003900012Q0016000F00043Q0020480010000B00124Q000F000200022Q0016000D000F3Q00123D000F000B3Q002048000F000F000C2Q004D00103Q00032Q002900115Q001242001200133Q001242001300144Q00310011001300020020480012000B00152Q00410010001100122Q002900115Q001242001200163Q001242001300174Q00310011001300020020480012000B00182Q00410010001100122Q002900115Q001242001200193Q0012420013001A4Q00310011001300020020480012000B001B2Q00410010001100124Q000F000200022Q0016000E000F3Q001242000C00023Q0004543Q0039000100061C00070032000100020004543Q003200012Q002200076Q002900085Q0012420009001C3Q001242000A001D4Q004A0008000A4Q003E00075Q0004543Q000200012Q00193Q00013Q00023Q00023Q00028Q0003053Q007063612Q6C00133Q0012423Q00014Q002C000100023Q0026153Q0002000100010004543Q0002000100123D000300023Q00062100043Q000100022Q001B8Q001B3Q00014Q000C0003000200042Q0016000200044Q0016000100033Q0006110001000F00013Q0004543Q000F000100060100030010000100020004543Q001000012Q002C000300034Q0040000300023Q0004543Q000200012Q00193Q00013Q00013Q00043Q0003043Q0067616D6503073Q00482Q747047657403153Q00B342DDB0290A7F8EBA46C0EE334039C7A218C6B23D03083Q00A1DB36A9C05A3050000B4Q00297Q00123D000100013Q00203C0001000100022Q0029000300013Q001242000400033Q001242000500044Q004A000300054Q005600016Q00328Q003E8Q00193Q00017Q00033Q0003053Q006D61746368030C3Q003CFF987D914CF7C272CA48FE03053Q00B962DAEB5701083Q00203C00013Q00012Q002900035Q001242000400023Q001242000500034Q004A000300054Q003200016Q003E00016Q00193Q00017Q00", GetFEnv(), ...);
