import sys
from typing import Callable, Any, TypeVar, NamedTuple
from math import floor
from itertools import count

import module_ as module_
import _dafny as _dafny
import System_ as System_

# Module: Huffman

class default__:
    def  __init__(self):
        pass

    @staticmethod
    def Weight(t):
        return (t).w

    @staticmethod
    def PrefixMap(b, m):
        def iife0_():
            coll0_ = _dafny.Map()
            compr_0_: TypeVar('Sym__')
            for compr_0_ in ((m).keys).Elements:
                d_0_s_: TypeVar('Sym__') = compr_0_
                if (d_0_s_) in ((m).keys):
                    coll0_[d_0_s_] = (_dafny.SeqWithoutIsStrInference([b])) + ((m)[d_0_s_])
            return _dafny.Map(coll0_)
        return iife0_()
        

    @staticmethod
    def Codes(t):
        source0_ = t
        if True:
            if source0_.is_Leaf:
                d_0_s_ = source0_.sym
                return _dafny.Map({d_0_s_: _dafny.SeqWithoutIsStrInference([])})
        if True:
            d_1_l_ = source0_.left
            d_2_r_ = source0_.right
            return (default__.PrefixMap(False, default__.Codes(d_1_l_))) | (default__.PrefixMap(True, default__.Codes(d_2_r_)))

    @staticmethod
    def IsPrefix(a, b):
        def lambda0_(forall_var_0_):
            d_0_i_: int = forall_var_0_
            return not (((0) <= (d_0_i_)) and ((d_0_i_) < (len(a)))) or (((a)[d_0_i_]) == ((b)[d_0_i_]))

        return ((len(a)) <= (len(b))) and (_dafny.quantifier(_dafny.IntegerRange(0, len(a)), True, lambda0_))

    @staticmethod
    def PrefixFreeMap(m):
        def lambda0_(forall_var_0_):
            def lambda1_(forall_var_1_):
                d_1_t_: TypeVar('Sym__') = forall_var_1_
                return not ((((d_0_s_) in ((m).keys)) and ((d_1_t_) in ((m).keys))) and ((d_0_s_) != (d_1_t_))) or ((not(default__.IsPrefix((m)[d_0_s_], (m)[d_1_t_]))) and (not(default__.IsPrefix((m)[d_1_t_], (m)[d_0_s_]))))

            d_0_s_: TypeVar('Sym__') = forall_var_0_
            return _dafny.quantifier(((m).keys).Elements, True, lambda1_)

        return _dafny.quantifier(((m).keys).Elements, True, lambda0_)

    @staticmethod
    def EncodeWithCodes(code, msg):
        d_0___accumulator_ = _dafny.SeqWithoutIsStrInference([])
        while True:
            with _dafny.label():
                if (len(msg)) == (0):
                    return (d_0___accumulator_) + (_dafny.SeqWithoutIsStrInference([]))
                elif True:
                    d_0___accumulator_ = (d_0___accumulator_) + ((code)[(msg)[0]])
                    in0_ = code
                    in1_ = _dafny.SeqWithoutIsStrInference((msg)[1::])
                    code = in0_
                    msg = in1_
                    raise _dafny.TailCall()
                break

    @staticmethod
    def Encode(t, msg):
        return default__.EncodeWithCodes(default__.Codes(t), msg)

    @staticmethod
    def DecodeOneFrom(node, bits):
        while True:
            with _dafny.label():
                source0_ = node
                if True:
                    if source0_.is_Leaf:
                        d_0_s_ = source0_.sym
                        return Option_Some((d_0_s_, bits))
                if True:
                    d_1_l_ = source0_.left
                    d_2_r_ = source0_.right
                    if (len(bits)) == (0):
                        return Option_None()
                    elif not((bits)[0]):
                        in0_ = d_1_l_
                        in1_ = _dafny.SeqWithoutIsStrInference((bits)[1::])
                        node = in0_
                        bits = in1_
                        raise _dafny.TailCall()
                    elif True:
                        in2_ = d_2_r_
                        in3_ = _dafny.SeqWithoutIsStrInference((bits)[1::])
                        node = in2_
                        bits = in3_
                        raise _dafny.TailCall()
                break

    @staticmethod
    def DecodeOptionFuel(t, bits, fuel):
        if (len(bits)) == (0):
            return Option_Some(_dafny.SeqWithoutIsStrInference([]))
        elif (fuel) == (0):
            return Option_None()
        elif True:
            source0_ = default__.DecodeOneFrom(t, bits)
            if True:
                if source0_.is_None:
                    return Option_None()
            if True:
                d_0_p_ = source0_.value
                source1_ = default__.DecodeOptionFuel(t, (d_0_p_)[1], (fuel) - (1))
                if True:
                    if source1_.is_None:
                        return Option_None()
                if True:
                    d_1_restMsg_ = source1_.value
                    return Option_Some((_dafny.SeqWithoutIsStrInference([(d_0_p_)[0]])) + (d_1_restMsg_))

    @staticmethod
    def DecodeOption(t, bits):
        return default__.DecodeOptionFuel(t, bits, len(bits))

    @staticmethod
    def CountOf(msg, x):
        d_0___accumulator_ = 0
        while True:
            with _dafny.label():
                if (len(msg)) == (0):
                    return (0) + (d_0___accumulator_)
                elif True:
                    d_0___accumulator_ = (d_0___accumulator_) + ((1 if ((msg)[0]) == (x) else 0))
                    in0_ = _dafny.SeqWithoutIsStrInference((msg)[1::])
                    in1_ = x
                    msg = in0_
                    x = in1_
                    raise _dafny.TailCall()
                break

    @staticmethod
    def DistinctSymbols(msg):
        syms: _dafny.Seq = _dafny.Seq({})
        d_0_acc_: _dafny.Seq
        d_0_acc_ = _dafny.SeqWithoutIsStrInference([])
        d_1_i_: int
        d_1_i_ = 0
        while (d_1_i_) < (len(msg)):
            if ((msg)[d_1_i_]) in (d_0_acc_):
                d_1_i_ = (d_1_i_) + (1)
            elif True:
                d_2_oldAcc_: _dafny.Seq
                d_2_oldAcc_ = d_0_acc_
                d_0_acc_ = (d_2_oldAcc_) + (_dafny.SeqWithoutIsStrInference([(msg)[d_1_i_]]))
                d_1_i_ = (d_1_i_) + (1)
        syms = d_0_acc_
        return syms

    @staticmethod
    def BuildFreqFromMsg(msg):
        freq: _dafny.Seq = _dafny.Seq({})
        d_0_syms_: _dafny.Seq
        out0_: _dafny.Seq
        out0_ = default__.DistinctSymbols(msg)
        d_0_syms_ = out0_
        freq = _dafny.SeqWithoutIsStrInference([])
        d_1_i_: int
        d_1_i_ = 0
        while (d_1_i_) < (len(d_0_syms_)):
            d_2_s_: TypeVar('Sym__')
            d_2_s_ = (d_0_syms_)[d_1_i_]
            d_3_w_: int
            d_3_w_ = default__.CountOf(msg, d_2_s_)
            d_4_oldFreq_: _dafny.Seq
            d_4_oldFreq_ = freq
            freq = (d_4_oldFreq_) + (_dafny.SeqWithoutIsStrInference([(d_2_s_, d_3_w_)]))
            d_1_i_ = (d_1_i_) + (1)
        return freq

    @staticmethod
    def BuildHuffmanFromMsg(msg):
        t: HTree = None
        d_0_freq_: _dafny.Seq
        out0_: _dafny.Seq
        out0_ = default__.BuildFreqFromMsg(msg)
        d_0_freq_ = out0_
        out1_: HTree
        out1_ = default__.BuildHuffman(d_0_freq_)
        t = out1_
        return t

    @staticmethod
    def InsertSorted(q, t):
        d_0___accumulator_ = _dafny.SeqWithoutIsStrInference([])
        while True:
            with _dafny.label():
                if (len(q)) == (0):
                    return (d_0___accumulator_) + (_dafny.SeqWithoutIsStrInference([t]))
                elif (default__.Weight(t)) <= (default__.Weight((q)[0])):
                    return (d_0___accumulator_) + ((_dafny.SeqWithoutIsStrInference([t])) + (q))
                elif True:
                    d_0___accumulator_ = (d_0___accumulator_) + (_dafny.SeqWithoutIsStrInference([(q)[0]]))
                    in0_ = _dafny.SeqWithoutIsStrInference((q)[1::])
                    in1_ = t
                    q = in0_
                    t = in1_
                    raise _dafny.TailCall()
                break

    @staticmethod
    def CheckPrefixFree(t):
        ok: bool = False
        ok = True
        return ok

    @staticmethod
    def BuildHuffman(freq):
        t: HTree = None
        d_0_q_: _dafny.Seq
        d_0_q_ = _dafny.SeqWithoutIsStrInference([])
        d_1_i_: int
        d_1_i_ = 0
        while (d_1_i_) < (len(freq)):
            d_2_s_: TypeVar('Sym__')
            d_2_s_ = ((freq)[d_1_i_])[0]
            d_3_w_: int
            d_3_w_ = ((freq)[d_1_i_])[1]
            d_4_leaf_: HTree
            d_4_leaf_ = HTree_Leaf(d_2_s_, d_3_w_)
            d_5_oldq_: _dafny.Seq
            d_5_oldq_ = d_0_q_
            d_0_q_ = default__.InsertSorted(d_5_oldq_, d_4_leaf_)
            d_1_i_ = (d_1_i_) + (1)
        while (len(d_0_q_)) > (1):
            d_6_oldq_: _dafny.Seq
            d_6_oldq_ = d_0_q_
            d_7_a_: HTree
            d_7_a_ = (d_6_oldq_)[0]
            d_8_b_: HTree
            d_8_b_ = (d_6_oldq_)[1]
            d_9_rest_: _dafny.Seq
            d_9_rest_ = _dafny.SeqWithoutIsStrInference((d_6_oldq_)[2::])
            d_10_merged_: HTree
            d_10_merged_ = HTree_Node((default__.Weight(d_7_a_)) + (default__.Weight(d_8_b_)), d_7_a_, d_8_b_)
            d_0_q_ = default__.InsertSorted(d_9_rest_, d_10_merged_)
        t = (d_0_q_)[0]
        return t

    @staticmethod
    def CRC(msg):
        return default__.CRCAcc(msg, 0)

    @staticmethod
    def CRCAcc(msg, acc):
        while True:
            with _dafny.label():
                if (len(msg)) == (0):
                    return acc
                elif True:
                    d_0_next_ = _dafny.euclidian_modulus(((acc) * (257)) + (ord((msg)[0])), 65536)
                    in0_ = _dafny.SeqWithoutIsStrInference((msg)[1::])
                    in1_ = d_0_next_
                    msg = in0_
                    acc = in1_
                    raise _dafny.TailCall()
                break

    @staticmethod
    def WrapMsg(msg):
        d_0___accumulator_ = _dafny.SeqWithoutIsStrInference([])
        while True:
            with _dafny.label():
                if (len(msg)) == (0):
                    return (d_0___accumulator_) + (_dafny.SeqWithoutIsStrInference([]))
                elif True:
                    d_0___accumulator_ = (d_0___accumulator_) + (_dafny.SeqWithoutIsStrInference([WSym_Real((msg)[0])]))
                    in0_ = _dafny.SeqWithoutIsStrInference((msg)[1::])
                    msg = in0_
                    raise _dafny.TailCall()
                break

    @staticmethod
    def UnwrapMsg(wmsg):
        d_0___accumulator_ = _dafny.SeqWithoutIsStrInference([])
        while True:
            with _dafny.label():
                if (len(wmsg)) == (0):
                    return (d_0___accumulator_) + (_dafny.SeqWithoutIsStrInference([]))
                elif True:
                    d_0___accumulator_ = (d_0___accumulator_) + (_dafny.SeqWithoutIsStrInference([((wmsg)[0]).s]))
                    in0_ = _dafny.SeqWithoutIsStrInference((wmsg)[1::])
                    wmsg = in0_
                    raise _dafny.TailCall()
                break

    @staticmethod
    def SafeBuildHuffmanFromMsg(msg):
        t: HTree = HTree.default(WSym.default())()
        d_0_augmented_: _dafny.Seq
        d_0_augmented_ = (default__.WrapMsg(msg)) + (_dafny.SeqWithoutIsStrInference([WSym_Sentinel()]))
        out0_: HTree
        out0_ = default__.BuildHuffmanFromMsg(d_0_augmented_)
        t = out0_
        return t

    @staticmethod
    def SafeEncode(t, msg):
        bits: _dafny.Seq = _dafny.Seq({})
        bits = default__.Encode(t, default__.WrapMsg(msg))
        return bits

    @staticmethod
    def SafeDecodeOption(t, bits):
        res: Option = Option.default()()
        d_0_wres_: Option
        d_0_wres_ = default__.DecodeOption(t, bits)
        source0_ = d_0_wres_
        with _dafny.label("match0"):
            if True:
                if source0_.is_None:
                    res = Option_None()
                    raise _dafny.Break("match0")
            if True:
                d_1_wmsg_ = source0_.value
                d_2_allReal_: bool
                d_2_allReal_ = True
                d_3_i_: int
                d_3_i_ = 0
                while (d_3_i_) < (len(d_1_wmsg_)):
                    if not(((d_1_wmsg_)[d_3_i_]).is_Real):
                        d_2_allReal_ = False
                    d_3_i_ = (d_3_i_) + (1)
                if d_2_allReal_:
                    res = Option_Some(default__.UnwrapMsg(d_1_wmsg_))
                elif True:
                    res = Option_None()
            pass
        return res

    @staticmethod
    def SafeCheckRoundTrip(t, msg):
        ok: bool = False
        ok = True
        return ok

    @staticmethod
    def SafeEncodeWithCRC(t, msg):
        bits: _dafny.Seq = _dafny.Seq({})
        crc: int = int(0)
        out0_: _dafny.Seq
        out0_ = default__.SafeEncode(t, msg)
        bits = out0_
        crc = default__.CRC(msg)
        return bits, crc

    @staticmethod
    def SafeDecodeWithCRC(t, bits, expectedCRC):
        res: Option = Option.default()()
        d_0_decoded_: Option
        out0_: Option
        out0_ = default__.SafeDecodeOption(t, bits)
        d_0_decoded_ = out0_
        if (d_0_decoded_).is_Some:
            if (default__.CRC((d_0_decoded_).value)) == (expectedCRC):
                res = Option_Some((d_0_decoded_).value)
            elif True:
                res = Option_None()
        elif True:
            res = Option_None()
        return res

    @staticmethod
    def SafeDecodeEncodedMessage(t, msg):
        decoded: _dafny.Seq = _dafny.Seq({})
        d_0_wdecoded_: Option
        d_0_wdecoded_ = default__.DecodeOption(t, default__.Encode(t, default__.WrapMsg(msg)))
        decoded = default__.UnwrapMsg((d_0_wdecoded_).value)
        return decoded


class Option:
    @classmethod
    def default(cls, ):
        return lambda: Option_None()
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_None(self) -> bool:
        return isinstance(self, Option_None)
    @property
    def is_Some(self) -> bool:
        return isinstance(self, Option_Some)

class Option_None(Option, NamedTuple('None_', [])):
    def __dafnystr__(self) -> str:
        return f'Huffman.Option.None'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, Option_None)
    def __hash__(self) -> int:
        return super().__hash__()

class Option_Some(Option, NamedTuple('Some', [('value', Any)])):
    def __dafnystr__(self) -> str:
        return f'Huffman.Option.Some({_dafny.string_of(self.value)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, Option_Some) and self.value == __o.value
    def __hash__(self) -> int:
        return super().__hash__()


class HTree:
    @classmethod
    def default(cls, default_Sym):
        return lambda: HTree_Leaf(default_Sym(), int(0))
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_Leaf(self) -> bool:
        return isinstance(self, HTree_Leaf)
    @property
    def is_Node(self) -> bool:
        return isinstance(self, HTree_Node)

class HTree_Leaf(HTree, NamedTuple('Leaf', [('sym', Any), ('w', Any)])):
    def __dafnystr__(self) -> str:
        return f'Huffman.HTree.Leaf({_dafny.string_of(self.sym)}, {_dafny.string_of(self.w)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, HTree_Leaf) and self.sym == __o.sym and self.w == __o.w
    def __hash__(self) -> int:
        return super().__hash__()

class HTree_Node(HTree, NamedTuple('Node', [('w', Any), ('left', Any), ('right', Any)])):
    def __dafnystr__(self) -> str:
        return f'Huffman.HTree.Node({_dafny.string_of(self.w)}, {_dafny.string_of(self.left)}, {_dafny.string_of(self.right)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, HTree_Node) and self.w == __o.w and self.left == __o.left and self.right == __o.right
    def __hash__(self) -> int:
        return super().__hash__()


class WSym:
    @classmethod
    def default(cls, ):
        return lambda: WSym_Sentinel()
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_Real(self) -> bool:
        return isinstance(self, WSym_Real)
    @property
    def is_Sentinel(self) -> bool:
        return isinstance(self, WSym_Sentinel)

class WSym_Real(WSym, NamedTuple('Real', [('s', Any)])):
    def __dafnystr__(self) -> str:
        return f'Huffman.WSym.Real({_dafny.string_of(self.s)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, WSym_Real) and self.s == __o.s
    def __hash__(self) -> int:
        return super().__hash__()

class WSym_Sentinel(WSym, NamedTuple('Sentinel', [])):
    def __dafnystr__(self) -> str:
        return f'Huffman.WSym.Sentinel'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, WSym_Sentinel)
    def __hash__(self) -> int:
        return super().__hash__()

