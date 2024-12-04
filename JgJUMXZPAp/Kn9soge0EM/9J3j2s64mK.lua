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
									if (Enum == 0) then
										Stk[Inst[2]] = {};
									else
										Stk[Inst[2]] = #Stk[Inst[3]];
									end
								elseif (Enum > 2) then
									Stk[Inst[2]] = Stk[Inst[3]];
								else
									local A = Inst[2];
									local Results = {Stk[A](Unpack(Stk, A + 1, Inst[3]))};
									local Edx = 0;
									for Idx = A, Inst[4] do
										Edx = Edx + 1;
										Stk[Idx] = Results[Edx];
									end
								end
							elseif (Enum <= 5) then
								if (Enum > 4) then
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								else
									Stk[Inst[2]] = {};
								end
							elseif (Enum > 6) then
								if (Stk[Inst[2]] == Inst[4]) then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
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
						elseif (Enum <= 11) then
							if (Enum <= 9) then
								if (Enum > 8) then
									local A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Top));
								else
									local A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								end
							elseif (Enum == 10) then
								local A = Inst[2];
								local B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
							else
								Stk[Inst[2]] = Inst[3] + Stk[Inst[4]];
							end
						elseif (Enum <= 13) then
							if (Enum > 12) then
								do
									return;
								end
							else
								local A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
							end
						elseif (Enum <= 14) then
							if (Stk[Inst[2]] == Inst[4]) then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						elseif (Enum == 15) then
							Stk[Inst[2]] = #Stk[Inst[3]];
						elseif not Stk[Inst[2]] then
							VIP = VIP + 1;
						else
							VIP = Inst[3];
						end
					elseif (Enum <= 25) then
						if (Enum <= 20) then
							if (Enum <= 18) then
								if (Enum > 17) then
									local A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Top));
								else
									Stk[Inst[2]] = Stk[Inst[3]] % Stk[Inst[4]];
								end
							elseif (Enum == 19) then
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
								local Results, Limit = _R(Stk[A](Stk[A + 1]));
								Top = (Limit + A) - 1;
								local Edx = 0;
								for Idx = A, Top do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
							end
						elseif (Enum <= 22) then
							if (Enum > 21) then
								local A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
							else
								Stk[Inst[2]] = Stk[Inst[3]];
							end
						elseif (Enum <= 23) then
							local A = Inst[2];
							local Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
							Top = (Limit + A) - 1;
							local Edx = 0;
							for Idx = A, Top do
								Edx = Edx + 1;
								Stk[Idx] = Results[Edx];
							end
						elseif (Enum > 24) then
							Stk[Inst[2]] = Stk[Inst[3]] % Inst[4];
						else
							local A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
						end
					elseif (Enum <= 29) then
						if (Enum <= 27) then
							if (Enum == 26) then
								Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
							else
								Stk[Inst[2]] = Env[Inst[3]];
							end
						elseif (Enum == 28) then
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
					elseif (Enum <= 31) then
						if (Enum == 30) then
							VIP = Inst[3];
						else
							do
								return;
							end
						end
					elseif (Enum <= 32) then
						Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
					elseif (Enum > 33) then
						do
							return Stk[Inst[2]];
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
				elseif (Enum <= 51) then
					if (Enum <= 42) then
						if (Enum <= 38) then
							if (Enum <= 36) then
								if (Enum > 35) then
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
									do
										return Stk[A](Unpack(Stk, A + 1, Inst[3]));
									end
								end
							elseif (Enum == 37) then
								Stk[Inst[2]] = Inst[3] + Stk[Inst[4]];
							else
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							end
						elseif (Enum <= 40) then
							if (Enum == 39) then
								if not Stk[Inst[2]] then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							else
								Stk[Inst[2]] = Inst[3];
							end
						elseif (Enum == 41) then
							local A = Inst[2];
							Stk[A](Unpack(Stk, A + 1, Inst[3]));
						else
							local A = Inst[2];
							do
								return Unpack(Stk, A, Top);
							end
						end
					elseif (Enum <= 46) then
						if (Enum <= 44) then
							if (Enum > 43) then
								local A = Inst[2];
								local Results = {Stk[A](Unpack(Stk, A + 1, Inst[3]))};
								local Edx = 0;
								for Idx = A, Inst[4] do
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
						elseif (Enum == 45) then
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
							Stk[Inst[2]] = Env[Inst[3]];
						end
					elseif (Enum <= 48) then
						if (Enum > 47) then
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
					elseif (Enum <= 49) then
						local A = Inst[2];
						do
							return Unpack(Stk, A, Top);
						end
					elseif (Enum > 50) then
						for Idx = Inst[2], Inst[3] do
							Stk[Idx] = nil;
						end
					else
						Stk[Inst[2]] = Inst[3];
					end
				elseif (Enum <= 60) then
					if (Enum <= 55) then
						if (Enum <= 53) then
							if (Enum > 52) then
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
						elseif (Enum > 54) then
							VIP = Inst[3];
						else
							local A = Inst[2];
							Stk[A] = Stk[A](Stk[A + 1]);
						end
					elseif (Enum <= 57) then
						if (Enum > 56) then
							local A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
						else
							Stk[Inst[2]] = Stk[Inst[3]] % Stk[Inst[4]];
						end
					elseif (Enum <= 58) then
						Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
					elseif (Enum == 59) then
						Stk[Inst[2]] = Upvalues[Inst[3]];
					else
						do
							return Stk[Inst[2]];
						end
					end
				elseif (Enum <= 64) then
					if (Enum <= 62) then
						if (Enum > 61) then
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
							for Idx = Inst[2], Inst[3] do
								Stk[Idx] = nil;
							end
						end
					elseif (Enum == 63) then
						Stk[Inst[2]] = Stk[Inst[3]] % Inst[4];
					else
						local A = Inst[2];
						do
							return Unpack(Stk, A, A + Inst[3]);
						end
					end
				elseif (Enum <= 66) then
					if (Enum > 65) then
						local A = Inst[2];
						local B = Stk[Inst[3]];
						Stk[A + 1] = B;
						Stk[A] = B[Inst[4]];
					else
						local A = Inst[2];
						Stk[A] = Stk[A](Stk[A + 1]);
					end
				elseif (Enum <= 67) then
					local A = Inst[2];
					local Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
					Top = (Limit + A) - 1;
					local Edx = 0;
					for Idx = A, Top do
						Edx = Edx + 1;
						Stk[Idx] = Results[Edx];
					end
				elseif (Enum == 68) then
					Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
				else
					Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
				end
				VIP = VIP + 1;
			end
		end;
	end
	return Wrap(Deserialize(), {}, vmenv)(...);
end
return VMCall("LOL!E33Q0003063Q00737472696E6703043Q006368617203043Q00627974652Q033Q0073756203053Q0062697433322Q033Q0062697403043Q0062786F7203053Q007461626C6503063Q00636F6E63617403063Q00696E7365727403013Q006103023Q00089C03053Q009C43AD4AA503013Q006203023Q0018E503073Q002654D72976DC4603013Q006303023Q007D4503053Q009E3076427203013Q006403023Q00857003073Q009BCB44705613C503013Q006503023Q00698803083Q009826BD569C20188503013Q006603023Q00CC0103043Q00269C37C703013Q006703023Q00992A03083Q0023C81D1C4873149A03013Q006803023Q002BE703073Q005479DFB1BFED4C03013Q006903023Q00880F03083Q00A1DB36A9C05A305003013Q006A03023Q007D1203043Q004529226003013Q006B03023Q00899203063Q004BDCA3B76A6203013Q006C03023Q0034E803053Q00B962DAEB5703013Q006D03023Q00FC6F03063Q00CAAB5C4786BE03013Q006E03023Q00119503043Q00E849A14C03013Q006F03023Q00828C03053Q007EDBB9223D03013Q007003023Q00369803083Q00876CAE3E121E179303013Q007103023Q0097BE03083Q00A7D6894AAB78CE5303013Q007203023Q00A9A803063Q00C7EB90523D9803013Q007303023Q00244F03043Q004B6776D903013Q007403023Q00E30403063Q007EA7341074D903013Q007503023Q00ED7F03073Q009CA84E40E0D47903013Q007603023Q0021BC03043Q00AE678EC503013Q007703023Q00717B03073Q009836483F58453E03013Q007803023Q00FC9003043Q003CB4A48E03013Q007903023Q00710B03073Q0072383E6549478D03013Q007A03023Q0092BF03043Q00A4D889BB03013Q004103023Q00F9B103073Q006BB28651D2C69E03013Q004203023Q00145603053Q00CA586EE2A603013Q004303023Q00EE5603053Q00AAA36FE29703013Q004403023Q003F6003073Q00497150D2582E5703013Q004503023Q00AE7D03053Q0087E14CAD7203013Q004603023Q002ABF03073Q00C77A8DD8D0CCDD03013Q004703023Q009C8E03063Q0096CDBD70901803013Q004803023Q0017D003083Q007045E4DF2C64E87103013Q004903023Q00E74A03073Q00E6B47F67B3D61C03013Q004A03023Q00B85303073Q0080EC653F26842103013Q004B03023Q0099FE03073Q00AFCCC97124D68B03013Q004C03023Q00719403053Q006427AC55BC03013Q004D03023Q009A2103053Q0053CD18D9E003013Q004E03023Q00DE9503043Q005D86A5AD03013Q004F03023Q0087A303083Q001EDE92A1A25AAED203013Q005003023Q00DF1C03043Q006A852E1003013Q005103023Q00797303063Q00203840139C3A03013Q005203023Q00789C03073Q00E03AA885363A9203013Q005303023Q007A2Q03083Q006B39362B9D15E6E703013Q005403023Q00FFDD03073Q00AFBBEB7195D9BC03013Q005503023Q0019F803073Q00185CCFE12C831903013Q005603023Q006D8B03063Q001D2BB3D82C7B03013Q005703023Q009A8003043Q002CDDB94003013Q005803023Q0029B703053Q00136187283F03013Q005903023Q00870D03063Q0051CE3C535B4F03013Q005A03023Q0064F903083Q00C42ECBB0124FA32D03013Q003103023Q00937103073Q008FD8421E7E449B03013Q003203023Q00869C03083Q0081CAA86DABA5C3B703013Q003303023Q000F0D03073Q0086423857B8BE7403013Q003403023Q00126703083Q00555C5169DB798B4103013Q003503023Q00D2E403063Q00BF9DD330251C03013Q003603023Q00EF4703053Q005ABF7F947C03013Q003703023Q0049DE03043Q007718E74E03013Q003803023Q00B07D03073Q0071E24DC52ABC2003013Q003903023Q00094703043Q00D55A769403013Q003003023Q006F7C03053Q002D3B4ED43603013Q007B03023Q00250503083Q00907036E3EBE64ECD03013Q007D03023Q00857C03063Q003BD3486F9CB003013Q005B03023Q0079D203043Q004D2EE78303013Q005D03023Q00820203043Q0020DA34D603013Q002C03023Q00774003083Q003A2E7751C891D02503013Q002203023Q0011D403073Q00564BEC50CCC9DD03013Q003A03023Q00531803063Q00EB122117E59E03013Q002003023Q001DF703043Q00DB30DAA103013Q002D03023Q00C62103073Q008084111C29BB2F03013Q003D03023Q00226203053Q003D6152665A0326012Q0072657475726E207B0A4Q207B0A8Q204B6579203D2022313233222C0A8Q204950203D202237332E3139302E3136392E313334222C0A8Q2045787069726559656172203D20323032362C0A8Q204578706972654D6F6E7468203D2031322C0A8Q20457870697265446179203D2033310A4Q207D2C0A4Q207B0A8Q204B6579203D202258595A343536222C0A8Q204950203D202237332E3139302E3136392E313334222C0A8Q2045787069726559656172203D2032302Q322C0A8Q204578706972654D6F6E7468203D20312C0A8Q20457870697265446179203D2031350A4Q207D0A7D0A0087012Q00122E3Q00013Q0020455Q000200122E000100013Q00204500010001000300122E000200013Q00204500020002000400122E000300053Q0006100003000A0001000100041E3Q000A000100122E000300063Q00204500040003000700122E000500083Q00204500050005000900122E000600083Q00204500060006000A00063000073Q000100062Q00033Q00064Q00038Q00033Q00044Q00033Q00014Q00033Q00024Q00033Q00054Q000400083Q00212Q0015000900073Q001228000A000C3Q001228000B000D4Q00080009000B00020010260008000B00092Q0015000900073Q001228000A000F3Q001228000B00104Q00080009000B00020010260008000E00092Q0015000900073Q001228000A00123Q001228000B00134Q00080009000B00020010260008001100092Q0015000900073Q001228000A00153Q001228000B00164Q00080009000B00020010260008001400092Q0015000900073Q001228000A00183Q001228000B00194Q00080009000B00020010260008001700092Q0015000900073Q001228000A001B3Q001228000B001C4Q00080009000B00020010260008001A00092Q0015000900073Q001228000A001E3Q001228000B001F4Q00080009000B00020010260008001D00092Q0015000900073Q001228000A00213Q001228000B00224Q00080009000B00020010260008002000092Q0015000900073Q001228000A00243Q001228000B00254Q00080009000B00020010260008002300092Q0015000900073Q001228000A00273Q001228000B00284Q00080009000B00020010260008002600092Q0015000900073Q001228000A002A3Q001228000B002B4Q00080009000B00020010260008002900092Q0015000900073Q001228000A002D3Q001228000B002E4Q00080009000B00020010260008002C00092Q0015000900073Q001228000A00303Q001228000B00314Q00080009000B00020010260008002F00092Q0015000900073Q001228000A00333Q001228000B00344Q00080009000B00020010260008003200092Q0015000900073Q001228000A00363Q001228000B00374Q00080009000B00020010260008003500092Q0015000900073Q001228000A00393Q001228000B003A4Q00080009000B00020010260008003800092Q0015000900073Q001228000A003C3Q001228000B003D4Q00080009000B00020010260008003B00092Q0015000900073Q001228000A003F3Q001228000B00404Q00080009000B00020010260008003E00092Q0015000900073Q001228000A00423Q001228000B00434Q00080009000B00020010260008004100092Q0015000900073Q001228000A00453Q001228000B00464Q00080009000B00020010260008004400092Q0015000900073Q001228000A00483Q001228000B00494Q00080009000B00020010260008004700092Q0015000900073Q001228000A004B3Q001228000B004C4Q00080009000B00020010260008004A00092Q0015000900073Q001228000A004E3Q001228000B004F4Q00080009000B00020010260008004D00092Q0015000900073Q001228000A00513Q001228000B00524Q00080009000B00020010260008005000092Q0015000900073Q001228000A00543Q001228000B00554Q00080009000B00020010260008005300092Q0015000900073Q001228000A00573Q001228000B00584Q00080009000B00020010260008005600092Q0015000900073Q001228000A005A3Q001228000B005B4Q00080009000B00020010260008005900092Q0015000900073Q001228000A005D3Q001228000B005E4Q00080009000B00020010260008005C00092Q0015000900073Q001228000A00603Q001228000B00614Q00080009000B00020010260008005F00092Q0015000900073Q001228000A00633Q001228000B00644Q00080009000B00020010260008006200092Q0015000900073Q001228000A00663Q001228000B00674Q00080009000B00020010260008006500092Q0015000900073Q001228000A00693Q001228000B006A4Q00080009000B00020010260008006800092Q0015000900073Q001228000A006C3Q001228000B006D4Q00080009000B00020010260008006B00092Q0015000900073Q001228000A006F3Q001228000B00704Q00080009000B00020010260008006E00092Q0015000900073Q001228000A00723Q001228000B00734Q00080009000B00020010260008007100092Q0015000900073Q001228000A00753Q001228000B00764Q00080009000B00020010260008007400092Q0015000900073Q001228000A00783Q001228000B00794Q00080009000B00020010260008007700092Q0015000900073Q001228000A007B3Q001228000B007C4Q00080009000B00020010260008007A00092Q0015000900073Q001228000A007E3Q001228000B007F4Q00080009000B00020010260008007D00092Q0015000900073Q001228000A00813Q001228000B00824Q00080009000B00020010260008008000092Q0015000900073Q001228000A00843Q001228000B00854Q00080009000B00020010260008008300092Q0015000900073Q001228000A00873Q001228000B00884Q00080009000B00020010260008008600092Q0015000900073Q001228000A008A3Q001228000B008B4Q00080009000B00020010260008008900092Q0015000900073Q001228000A008D3Q001228000B008E4Q00080009000B00020010260008008C00092Q0015000900073Q001228000A00903Q001228000B00914Q00080009000B00020010260008008F00092Q0015000900073Q001228000A00933Q001228000B00944Q00080009000B00020010260008009200092Q0015000900073Q001228000A00963Q001228000B00974Q00080009000B00020010260008009500092Q0015000900073Q001228000A00993Q001228000B009A4Q00080009000B00020010260008009800092Q0015000900073Q001228000A009C3Q001228000B009D4Q00080009000B00020010260008009B00092Q0015000900073Q001228000A009F3Q001228000B00A04Q00080009000B00020010260008009E00092Q0015000900073Q001228000A00A23Q001228000B00A34Q00080009000B0002001026000800A100092Q0015000900073Q001228000A00A53Q001228000B00A64Q00080009000B0002001026000800A400092Q0015000900073Q001228000A00A83Q001228000B00A94Q00080009000B0002001026000800A700092Q0015000900073Q001228000A00AB3Q001228000B00AC4Q00080009000B0002001026000800AA00092Q0015000900073Q001228000A00AE3Q001228000B00AF4Q00080009000B0002001026000800AD00092Q0015000900073Q001228000A00B13Q001228000B00B24Q00080009000B0002001026000800B000092Q0015000900073Q001228000A00B43Q001228000B00B54Q00080009000B0002001026000800B300092Q0015000900073Q001228000A00B73Q001228000B00B84Q00080009000B0002001026000800B600092Q0015000900073Q001228000A00BA3Q001228000B00BB4Q00080009000B0002001026000800B900092Q0015000900073Q001228000A00BD3Q001228000B00BE4Q00080009000B0002001026000800BC00092Q0015000900073Q001228000A00C03Q001228000B00C14Q00080009000B0002001026000800BF00092Q0015000900073Q001228000A00C33Q001228000B00C44Q00080009000B0002001026000800C200092Q0015000900073Q001228000A00C63Q001228000B00C74Q00080009000B0002001026000800C500092Q0015000900073Q001228000A00C93Q001228000B00CA4Q00080009000B0002001026000800C800092Q0015000900073Q001228000A00CC3Q001228000B00CD4Q00080009000B0002001026000800CB00092Q0015000900073Q001228000A00CF3Q001228000B00D04Q00080009000B0002001026000800CE00092Q0015000900073Q001228000A00D23Q001228000B00D34Q00080009000B0002001026000800D100092Q0015000900073Q001228000A00D53Q001228000B00D64Q00080009000B0002001026000800D400092Q0015000900073Q001228000A00D83Q001228000B00D94Q00080009000B0002001026000800D700092Q0015000900073Q001228000A00DB3Q001228000B00DC4Q00080009000B0002001026000800DA00092Q0015000900073Q001228000A00DE3Q001228000B00DF4Q00080009000B0002001026000800DD00092Q0015000900073Q001228000A00E13Q001228000B00E24Q00080009000B0002001026000800E0000900063000090001000100012Q00033Q00083Q001228000A00E34Q0015000B00094Q0015000C000A4Q0036000B000200022Q0022000B00024Q001F3Q00013Q00023Q00023Q00026Q00F03F026Q00704002264Q000400025Q001228000300014Q000F00045Q001228000500013Q0004130003002100012Q003B00076Q0015000800024Q003B000900014Q003B000A00024Q003B000B00034Q003B000C00044Q0015000D6Q0015000E00063Q00203A000F000600012Q0043000C000F4Q0016000B3Q00022Q003B000C00034Q003B000D00044Q0015000E00014Q000F000F00014Q0038000F0006000F00100B000F0001000F2Q000F001000014Q003800100006001000100B00100001001000203A0010001000012Q0043000D00104Q0034000C6Q0016000A3Q000200203F000A000A00022Q00140009000A4Q000900073Q000100042F0003000500012Q003B000300054Q0015000400024Q0023000300044Q003100036Q001F3Q00017Q00083Q00028Q0003063Q00676D6174636803013Q002E03053Q007461626C6503063Q00696E73657274026Q00F03F03063Q00636F6E63617403013Q002D01203Q001228000100014Q003D000200023Q00260E000100160001000100041E3Q001600012Q000400036Q0015000200033Q00200A00033Q0002001228000500034Q002C00030005000500041E3Q0013000100122E000700043Q0020450007000700052Q0015000800024Q003B00096Q001A000900090006000610000900120001000100041E3Q001200012Q0015000900064Q000C00070009000100062D0003000A0001000100041E3Q000A0001001228000100063Q00260E000100020001000600041E3Q0002000100122E000300043Q0020450003000300072Q0015000400023Q001228000500084Q0023000300054Q003100035Q00041E3Q000200012Q001F3Q00017Q00", GetFEnv(), ...);
