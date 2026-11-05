import YM.RG05Readout.Many.Arrival
import YM.RG05Readout.Aligned.Geometry
/-!
# Enlarge pipeline before Readout activation

Demand deterministic many apron at each root, counted against L setup.
Requires after-block prices; pals for appropriate Mallow call in UV builder.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG05Readout.Many
open Set Function Filter Lattice RG RG.Supply Wilson Precision MergeProof MergeProof.Accent
open PhysicalNext.Repeat Legato Bandage
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G:Gauge}{C:Family G}
set_option quotPrecheck false
def apron (A:Levels G) (m:ℕ):= (A.clock.J (m+1)+2)*(A.S.block m).val^4
structure Storage (C:Family G)(D:Address.Rail C):Prop where
   exactMoon : Moonlit C.path (apron C.path.levels) (renal C.path.levels) (far C.path.levels) D
   preMesh m: ((C.S.block m).val:ℝ) ≤ 1+Real.log (Lambda C.path.levels m)

-- Paying Moss on the true path.Q hasa param and works only here. Include launch proofs. Meter(stage) nonuniform ok.
variable {A:Sheet G} (X:Rolls A)
lemma installments {Y:Protection X}(Z:Delays Y):∃ V:Delays Y, Push.PriceCompiler.DelayLe Z V ∧ ∀ U:Delays Y,Push.PriceCompiler.DelayLe V U→∀ (i:ℕ)(x:ℝ), U.betaEntry i ≤ x → ((X.L i).val:ℝ) ≤ 1 +Real.log (2+Real.log x):=by -- namespace test
    have hZ:Tendsto (fun x:ℝ=>1+Real.log (2+Real.log x)) atTop atTop:= tendsto_atTop_add_const_left _ _ (Real.tendsto_log_atTop.comp (tendsto_atTop_add_const_left _ _ Real.tendsto_log_atTop))
    choose v h using (fun i:ℕ=> eventually_atTop.mp (hZ.eventually_ge_atTop (↑((X.L i).val):ℝ)))
    let V:Delays Y:= { Z with betaEntry:= fun i=>max (Z.betaEntry i) (v i) }; exact ⟨V,⟨fun i=> le_max_left ..,le_rfl,le_rfl,le_rfl⟩,fun U hu i x hx=> h i x ((le_max_right _ _).trans ((hu.beta i).trans hx))⟩

def triBlock (S:Schedule):Prop:=∀ i:ℕ,∃ j:ℕ,(S.block i).val=3^j
open Finset
omit X in
lemma threes (A:Sheet G) (hG:G.Simple):∃ U:Rolls A,∀ i:ℕ,∃ j:ℕ,(U.L i).val=3^j:=by
    choose v hp using (Rolls.eventually_large A hG)
    let M(i):= (Finset.range (i+1)).sup v
    have hv : Monotone M := fun i j hij=>Finset.sup_mono (range_mono (by omega))
    let L(i):Side:=⟨3^(M i), by positivity⟩
    refine ⟨⟨L,fun i=>hp i (L i) ?_ ?_,fun i j hz=>?_⟩,fun i=>⟨_,rfl⟩⟩
    · have he (n:ℕ): n+1 ≤ 3^n:=by induction n with
                                          | zero=>exact le_rfl
                                          | succ n ih=> rw [pow_succ]; omega
      exact ((Finset.le_sup (f:=v) (mem_range.mpr (by omega : i < i+1))).trans (M i|>.le_succ)).trans (he _)
    · exact (show Odd (3:ℕ) from ⟨1,rfl⟩).pow
    exact pow_le_pow_right₀ (show 1 ≤ (3:ℕ) by norm_num) (hv hz)
end YM.RG05Readout.Many
