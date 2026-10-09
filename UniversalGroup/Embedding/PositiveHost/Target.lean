module

public import UniversalGroup.Embedding.ProtectedInput.RowProduct
public import UniversalGroup.Embedding.PositiveHost.Model
public import UniversalGroup.Embedding.FactorSwap

@[expose] public section

/-!
# The protected factor-swap target in the positive host model

The full row/column product is faithful. Composing its row factor with the
protected basis change gives the ordered factors `(a,x)` and `(A,B,b)`.
-/

namespace UniversalGroup.Embedding.PositiveHost.Target

noncomputable section
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false

variable (G : PreparedInput) (D : ValievDatum G) (hi : ValievIntersections G D)

/-- Include the literal row group in the proper final extension. -/
def row : RowGroup G →* BaseModel.Model G D hi :=
  (RowProduct.row G (BaseModel.aGrid G D hi) (BaseModel.aGrid_injective G D hi)).comp
    (RowModel.toModel G)

theorem row_b : row G D hi (rowGeneratorB G) = BaseModel.b G D hi := by
  change RowProduct.row G (BaseModel.aGrid G D hi) (BaseModel.aGrid_injective G D hi)
    (RowModel.toModel G (rowGeneratorB G)) = _
  rw [RowModel.toModel_b]
  exact RowProduct.row_b G (BaseModel.aGrid G D hi) (BaseModel.aGrid_injective G D hi)

theorem row_c : row G D hi (rowGeneratorC G) = BaseModel.c G D hi := by
  change RowProduct.row G (BaseModel.aGrid G D hi) (BaseModel.aGrid_injective G D hi)
    (RowModel.toModel G (rowGeneratorC G)) = _
  rw [RowModel.toModel_c]
  change RowProduct.row G (BaseModel.aGrid G D hi) (BaseModel.aGrid_injective G D hi)
    (RowModel.of G (InputTriples.c G)) = _
  rw [RowProduct.row_of]
  exact BaseModel.embeddedGrid_c G D hi

/-- Interchange the factors and insert the protected ordered row triple. -/
def parameters : FactorSwapDomain →* RowModel.Model G × FreeGroup (Fin 2) where
  toFun p := (RowModel.toModel G (compressionTriple G p.2),p.1)
  map_one' := by simp
  map_mul' p q := by simp

theorem parameters_injective (hp : ProtectedRowTriple G) : Function.Injective (parameters G) := by
  intro p q hpq
  apply Prod.ext
  · exact congrArg Prod.snd hpq
  · exact (compressionTriple_injective G hp)
      ((RowModel.toModel_injective G) (congrArg Prod.fst hpq))

/-- The canonical model target, with factor order `(a,x;A,B,b)`. -/
def product : FactorSwapDomain →* BaseModel.Model G D hi :=
  (RowProduct.product G (BaseModel.aGrid G D hi) (BaseModel.aGrid_injective G D hi)).comp
    (parameters G)

theorem product_injective (hp : ProtectedRowTriple G) : Function.Injective (product G D hi) :=
  (RowProduct.product_injective G (BaseModel.aGrid G D hi) (BaseModel.aGrid_injective G D hi)).comp
    (parameters_injective G hp)

theorem product_apply (p : FactorSwapDomain) :
    product G D hi p = row G D hi (compressionTriple G p.2) * BaseModel.pair G D hi p.1 := rfl

theorem product_first (i : Fin 2) :
    product G D hi (factorFirst i) =
      ![BaseModel.a G D hi, (BaseModel.k G D hi)⁻¹ * BaseModel.f G D hi * BaseModel.k G D hi] i := by
  rw [product_apply]
  change row G D hi (compressionTriple G 1) * BaseModel.pair G D hi (FreeGroup.of i) = _
  rw [map_one, map_one, one_mul]
  fin_cases i
  · exact BaseModel.pair_a G D hi
  · exact BaseModel.pair_x G D hi

theorem product_second (i : Fin 3) :
    product G D hi (factorSecond i) =
      ![rowA (BaseModel.c G D hi) (BaseModel.b G D hi),
        rowB (BaseModel.c G D hi) (BaseModel.b G D hi), BaseModel.b G D hi] i := by
  rw [product_apply]
  change row G D hi (compressionTriple G (FreeGroup.of i)) * BaseModel.pair G D hi 1 = _
  rw [map_one,mul_one]
  fin_cases i
  · change row G D hi (compressionTriple G (FreeGroup.of 0)) =
      rowA (BaseModel.c G D hi) (BaseModel.b G D hi)
    have hh := congrArg (row G D hi) (compressionTriple_zero G)
    simpa only [map_mul, map_pow, map_inv, row_c, row_b, rowA, rowB] using hh
  · change row G D hi (compressionTriple G (FreeGroup.of 1)) =
      rowB (BaseModel.c G D hi) (BaseModel.b G D hi)
    have hh := congrArg (row G D hi) (compressionTriple_one G)
    simpa only [map_mul, map_inv, row_c, row_b, rowB] using hh
  · change row G D hi (compressionTriple G (FreeGroup.of 2)) = BaseModel.b G D hi
    have hh := congrArg (row G D hi) (compressionTriple_two G)
    simpa only [row_b] using hh

end
end UniversalGroup.Embedding.PositiveHost.Target
