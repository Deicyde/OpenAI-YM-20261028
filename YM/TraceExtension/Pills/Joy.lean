import YM.TraceExtension.Pills.Pollen
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Pills
open Function Filter Matrix Lattice Pressure Ac Wilson RG Precision Laurent Stationary Perfect Exterior Tree RG Wilson Finset Push.Uniform Det Planned.PrimaryIntegral295 Lamp
open Filch Turret Shepherd AnalyticBridge VerifiedReset Drupes Extra.Iteration SectorAffine Fen Kits
open scoped BigOperators Topology ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{n:Side} {P:Support n}{Q Q': Peat G n}{Y: Gal G n} {k:ℕ} {σ A C R D D' L:ℝ}
lemma stocks (hp:Clouded Y P) (he:∀ i:Lines G n 1,i.1∈P→ outD Q i=outD Q' i): rill Q Y=rill Q' Y:=by
   funext U; rw [hail,hail]; apply sum_congr rfl; intro i _; by_cases h:i.1∈ P; rw [he i h]; rw [hp.toes i U h]; ring
lemma husk {I:Type} (R:Rep G n)(v:I→Barley)(S:Finset I) (h:Clouded Y P) (he:2 ≤R.p.B): rill (piste R v S) Y=rill (prun R v P S) Y:=stocks h (fun i hi=>pruned R v P S i hi he)
lemma hymn {I:Type} (R:Rep G n) (v:I→Barley)(S:Finset I)(P:Support n): Drift _ (prun R v P S):=by
    intro X _ _ U x H; unfold Function.comp; simp only[prun,Finset.sum_apply]; exact ContDiffAt.sum fun i _=> Fen.lick R v i U x H
-- mixed all orders at pole.Splendor
structure Climate (Y:Gal G n) (k:ℕ) (A C:ℝ) :Prop where
    laps (V:Type)[NormedAddCommGroup V] [NormedSpace ℝ V](W:V→ Config G n)(x:V) : (∀ i, Allows (k+1) (fun y=>G.mat (W y i)) x C)→∀ i, Allows (k+1) (fun y=> Y (W y) i) x A
lemma allp (G:Gauge)(A:ℝ)(ha:0≤ A)(k:ℕ):∃ f:ℕ→ℝ,MarksP f∧∀ (n:Side) (x:Site n)(r:ℕ)(Y:Gal G n)(D a:ℝ),0 ≤a→0≤ D→ Y∈ rains G n→ Estate x (bottom Y) a (fun _=>D) → Climate (lakesY x r Y) k (f r*D) A:=by
   obtain ⟨f,hf,H⟩:=Turret.entire G (k+1) A ha
   exact ⟨f,hf,fun n x r Y D a hp hv h ht=>⟨fun V _ _ W y he i=> (H V n x D a r W y he hv hp).2 Y h ht i⟩⟩
-- use high grants.Cannot Splendor for rill. make Frozen weaker called Lodge.
def blare(G:Gauge)(P:Support n) (k:ℕ)(A C :ℝ):ℝ:= (P.card*Fintype.card (Loc G 1):ℕ)*(2^k*A*C)
structure HearthV (U:Peat G n)(P:Support n)(k:ℕ)(A C:ℝ):Prop where
   silk : U∈loom G n
   pillar : LocalOn P U
   symU: GaugeInvariant U
   choir : Drift _ U
   price(V:Type)[NormedAddCommGroup V][NormedSpace ℝ V](W:V→ Config G n)(x:V):(∀ i,Allows (k+1) (fun y=>G.mat (W y i)) x C)→Allows k (U ∘ W) x A
lemma phare(G:Gauge)(hG:G.Simple)(C:ℝ)(hc:0≤ C)(k:ℕ):∃ C':ℝ,0 ≤ C' ∧ ∀ (n:Side) (V:Gal G n)(F:Peat G n)(P:Support n)(D A:ℝ), Drift _ F→ Climate V k D C→ Clouded V P→Splendor F P (k+1) A C' →
    HearthV (rill F V) P k (blare G P k D A) C:=by
    obtain ⟨M,hM,H⟩:=pie_roll G (k+1) C hc
    refine ⟨M,hM,fun n V F P D A hF hV ht h=>?_⟩
    let f :=rill F V; refine ⟨rill_lo hF h.symm ht hG,rill_local h.locale ht.stout,rill_covU hF h.symm ht,rill_lit hF ht.wakes,?_⟩
    intro X _ _ W x hW; let S:=P ×ˢ (@univ (Loc G 1) _); let U(p:X×Link G n):=input _ _ p.2*W p.1
    have hv(i:Lines G n 1): Allows k (outD F i ∘ W) x A:= priced_partial (x:=x) (a:=bolt i) (h.tickets _ U (x,0) (H _ W x hW)) (norm_bolt _).le
    have hp(i):Allows k (fun y=> V (W y) i*outD F i (W y)) x (2^k*D*A):=by
        have hx:= ((hV.laps X W x hW i).order (k:=k) (by omega)).bilinear (ContinuousLinearMap.mul ℝ ℝ) (hv i) (ContinuousLinearMap.opNorm_mul_le ℝ ℝ); rw[mul_one] at hx; exact hx
    rw[show rill F V ∘ W=(fun x=> ∑ i∈S,V (W x) i*outD F i (W x)) from funext (fun x=>by rw[Function.comp_apply,hail]; apply Eq.symm (sum_subset (subset_univ _) ?_); intro i _ hi; rw [ht.toes i (W x) (fun h=> hi (mem_product.mpr ⟨h,mem_univ _⟩)),zero_mul])]; apply (allows_sum (f:=fun i y=>V (W y) i*outD F i (W y)) (s:=S) (fun i _=> hp i)).mono (le_of_eq ?_); simp only [sum_const, nsmul_eq_mul, S,card_product,card_univ]; rfl
end YM.Trace.Pills
