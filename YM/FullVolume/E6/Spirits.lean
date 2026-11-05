import YM.FullVolume.E6.Ether
import YM.FullVolume.E6.Sparse
/-! E6 Layout steps full volume.Epoch. Keep Records by exact tags.Canvas.Read.F. -/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Lim
open Function Filter Set Lattice RG Pressure Pressure.Tube Tree Wilson Finset MeasureTheory
open Shell Coat SliceRows Pulse Mask Raw Matter Pond
open Push Push.AbsoluteSums Gas Ursell Trees Multiple Letter OmitClusters RG Shoot Precision SectorMeasure Oriented Reserves
open AnalyticBridge VerifiedReset Collection Quotes UVNext Next.Scheduling Org
open Extra.Iteration PhysicalNext.Repeat Greenbelt Match Song Refrain
open Blaze Blaze.March Captain Silica Height Brim Time Supply Input Testing PriceCompiler Opera
open UVNext.CouplingReset Animals Progress.DirectedRecipe Ovens
open Stationary Stationary.Shade Stationary.Beacon Laurent Exterior Bloch
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {P : Teller G} {S : StepData c f} {F : Forest S.ratio}
open Matrix Window Progress.StationaryScenes Green Census Control Flux FullVolume.Shadow
open Gate Frond Vine Mask
variable {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E] {φ: Filter ℕ}{J: Ultrafilter ℕ}{Q:ConnectedActivityE6.Target G P}{W x μ C₀ a b e ℓ v :ℝ}{o:Target.Order G W}
    {Λ: Era G S}{U:ℕ→ E→ Config G c}{Z: Draft F G} {K H:ℕ→ Epoch Λ}{j:ℕ}{p:E}
open FullVolume.Neptune
-- non recyclable logIndex. real fixed sizes.R
abbrev Loose (i:Coat.LogIndex c f): Prop := ¬∃ j:ℕ,i=Sum.inl (Sum.inl j)
private lemma atomLeaves (b:ℕ) (d:ℕ) [NeZero d]:∃ v:Finset (Trans c),∀ p:Trans c, Shade.stretch d p.2.2 ≤ b → p∈ v:=by
    let x(k:ℕ):= chants d (-1) k
    have hp : Summable x:= silts d zero_lt_one; let z:=Real.exp (-(b:ℝ)); have hz:∀ᶠ i:ℕ in cofinite,x i<z:=hp.tendsto_cofinite_zero.eventually (gt_mem_nhds (Real.exp_pos _))
    obtain ⟨T,hT⟩:= eventually_atTop.mp (Nat.cofinite_eq_atTop ▸ hz)
    refine ⟨Finset.univ ×ˢ (Finset.univ ×ˢ Finset.range T),fun p hp=> mem_product.mpr ⟨mem_univ _,mem_product.mpr ⟨mem_univ _,mem_range.mpr ?_⟩⟩⟩
    by_contra! hi; apply lt_irrefl z ((hT _ hi).trans_le' (Real.exp_monotone ?_)); change -(b:ℝ) ≤ (-1 :ℝ)*_; simp only [neg_one_mul, neg_le_neg_iff, Nat.cast_le]; exact hp
private lemma duplexLeaves {a:Side} (A:Cad G)(k:ℕ): ∃ T:Finset (Pairs a),∀ i, Raw.bothCharge A.path i≤ k → i∈T:=by
    obtain ⟨T,hT⟩:=tagSet k
    refine ⟨Finset.univ ×ˢ (Finset.univ ×ˢ (Finset.univ ×ˢ (T ×ˢ T))),fun ⟨p,i,j,u,v⟩ hx=> mem_product.mpr ⟨mem_univ _,mem_product.mpr ⟨mem_univ _, mem_product.mpr ⟨mem_univ _,mem_product.mpr ⟨?_,?_⟩⟩⟩⟩⟩
    all_goals
       have he : Raw.bothCharge (A.path) (G:=G) ((p,i,j,u,v):Pairs a)=(Beacon.flag u).length+(Beacon.flag v).length:=by unfold Raw.bothCharge Paths.length; rw [Fin.sum_univ_two]; rfl
       apply hT; rw [he] at hx; dsimp only; omega
private lemma logs {b:ℕ}(R: Epoch Λ):∃ M:Finset (Raw.LogLetter c f),∀ i : Raw.LogLetter c f, Loose (Sum.inl i)→ Raw.extra R.tubes R.kin i≤ b→i∈ M:=by
    obtain ⟨T,hT⟩:=atomLeaves (c:=f) b 1; obtain ⟨P,hP⟩:=atomLeaves (c:=f) b 2; obtain ⟨Q,hQ⟩:=atomLeaves (c:=f) b 3
    obtain ⟨Y,hY⟩:= duplexLeaves (a:=c) R.down b; obtain ⟨X,hX⟩:=duplexLeaves (a:=f) R.up b
    refine ⟨(∅:Finset ℕ).disjSum (P.disjSum (Q.disjSum (T.disjSum (X.disjSum Y)))),?_⟩; rintro (i|i|i|i|i|i) hh hk
    · exact (hh ⟨i,rfl⟩).elim
    · apply inr_mem_disjSum.mpr (inl_mem_disjSum.mpr (hP i ?_)); exact le_trans (pervade (R.up.path.cubic) (fun _=>rfl) _).ge hk
    · apply inr_mem_disjSum.mpr (inr_mem_disjSum.mpr (inl_mem_disjSum.mpr (hQ i ?_))); exact le_trans (pervade (R.up.path.quartic) (fun _=>rfl) _).ge hk
    · apply inr_mem_disjSum.mpr (inr_mem_disjSum.mpr (inr_mem_disjSum.mpr (inl_mem_disjSum.mpr (hT i ?_)))); exact le_trans (pervade (R.up.path.loop) (fun _=>rfl) _).ge hk
    all_goals simp only [inr_mem_disjSum,inl_mem_disjSum]; first|exact hX i hk|exact hY i hk
namespace Epoch
lemma hamlets (A:Epoch Λ) (b:ℕ):∃ M:Finset (Coat.LogIndex c f),∀ i, Loose i→ exCharge A.tubes A.kin i≤ b → i∈ M:=by
    obtain ⟨T,hT⟩:=logs (b:=b) A
    let P(d:ℕ): Finset (Pulse.Itinerary.Ledger f d):= (Finset.range (b+1)).sigma (fun _=>Finset.univ)
    refine ⟨T.disjSum ((Finset.univ:Finset (Coat.Miniature c f)).disjSum ((P 3).disjSum ((P 3).disjSum ((P 1).disjSum (Finset.univ.disjSum (P 2)))))),?_⟩; rintro (i|i|i|i|i|i|i) hi hx
    · exact inl_mem_disjSum.mpr (hT i hi hx)
    · simp
    all_goals simp only [inr_mem_disjSum,inl_mem_disjSum]; first| exact mem_univ _| cases i; exact mem_sigma.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hx), mem_univ _⟩
end Epoch
end YM.ConnectedActivityE6.Lim
