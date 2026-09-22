import GALECParser.ProfileRules
import GALECParser.ProfileProofTactic

namespace Rumoca.GALEC.Structural.ProfileSemantics
open _root_.Parser LALR.Frontend StructuralActions
open Structural

set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

theorem scalar_words_yield (b : Syntax.Block) (word : List Token) :
    Words rules Token.symbol (.ref "program") word (ProfileProjection.ofScalar b) →
      word = b.tokens := by
  cases b
  intro h
  unpack_direct_words
  all_goals simp_all [Result, symbol_literal,
    ProfileProjection.ofScalar, ProfileProjection.startup,
    ProfileProjection.recalibrate, ProfileProjection.scalarStep,
    ProfileProjection.selfRef, Syntax.Block.tokens]

theorem scalar_words_ast (b : Syntax.Block) (ast : AST.Block) :
    Words rules Token.symbol (.ref "program") b.tokens ast →
      ast = ProfileProjection.ofScalar b := by
  cases b
  intro h
  unpack_direct_words
  all_goals simp_all [Result, symbol_literal,
    ProfileProjection.ofScalar, ProfileProjection.startup,
    ProfileProjection.recalibrate, ProfileProjection.scalarStep,
    ProfileProjection.selfRef, Syntax.Block.tokens]

theorem tensor_words_yield (b : Syntax.TensorBlock) (word : List Token) :
    Words rules Token.symbol (.ref "program") word (ProfileProjection.ofTensor b) →
      word = b.tokens := by
  cases b
  intro h
  unpack_direct_words
  all_goals simp_all [Result, symbol_literal,
    ProfileProjection.ofTensor, ProfileProjection.startup,
    ProfileProjection.recalibrate, ProfileProjection.tensorStep,
    ProfileProjection.product, ProfileProjection.selfRef,
    Syntax.TensorBlock.tokens]

theorem tensor_words_ast (b : Syntax.TensorBlock) (ast : AST.Block) :
    Words rules Token.symbol (.ref "program") b.tokens ast →
      ast = ProfileProjection.ofTensor b := by
  cases b
  intro h
  unpack_direct_words
  all_goals simp_all [Result, symbol_literal,
    ProfileProjection.ofTensor, ProfileProjection.startup,
    ProfileProjection.recalibrate, ProfileProjection.tensorStep,
    ProfileProjection.product, ProfileProjection.selfRef,
    Syntax.TensorBlock.tokens]

end Rumoca.GALEC.Structural.ProfileSemantics

