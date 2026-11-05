import YM.Planned.PRIMARY_INTEGRAL_295.Soaring
/-!
# Full genuine template pulls: earning remμ Ember from Quantum

Calendar pays extra ɛ-Music Only for these evaluations. Needs also gap/inversion
fees as simultaneous authorities. No changing anchor before Projection queries.
Every certificate is pointwise even though Caps aggregate; no derivative in
periods. Proves Service only below Forecast.Bed tolerance. -/
set_option autoImplicit false
noncomputable section
namespace YM.Planned.PrimaryIntegral295.Density
open Function Filter Set Metric
open Labels Lattice RG Wilson Pressure Precision Exterior Tree Streets Carrier Bloch Place
open Villa Fizz Fizz.Gush Bazaars Cedar Quire Oval
open Bunks Little Work.F01 Little.Core
open Progress.StationaryScenes.Green Push.Uniform Floor
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius RealInnerProductSpace Classical
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {G : Gauge} {z n k:ℕ} {c f:Side} {S : StepData c f}
variable {K : Core G S} {W:Lines S.ratio.count} {w: Trinket}
namespace Trinket
variable (w) (G:Gauge) (L:Side)
def piles (k:ℕ) (M t:ℝ) (R:ℕ) := w.C*t*flake k M+(w.C*Real.exp (-w.α*R))*M+
     (2^k*w.tone k M t*(w.C*M))*(bow G L w.α)
def traps (k:ℕ) (M t:ℝ) (R:ℕ):= 2^k*(2*w.C)*w.piles G L k M t R*(lease G L w.α)
lemma pills (k:ℕ) {M t:ℝ} (R:ℕ) (hM:0≤M) (ht:0≤t) :0≤w.piles G L k M t R := by
   have hp:=w.tone_ge k hM ht; have hb:= bow_ge G L w.wisdom; have hs:= w.witness; unfold piles flake; positivity

end Trinket
open Trinket
variable {t M:ℝ} {b:E→Dir G c}

def stripDawn (K:Core G S) (W:Lines S.ratio.count): Dir G c→L[ℝ] Temps G f:= ContinuousLinearMap.pi
    (fun i=> EuclideanSpace.proj (𝕜:=ℝ) i.2 ∘L ((ContinuousLinearMap.proj i.1) ∘L ((Streets.streamFill S _) ∘L (crick S K.tree W))))

abbrev patchedAt (K:Core G S) (b:E→Dir G c)(t:ℝ)(x:E) := t⁻¹ • K.epoxy (t • b x)
abbrev carriedAt (K:Core G S) (b:E→Dir G c)(W:Lines S.ratio.count) (x:E) := K.dawn (b x) W

namespace Guide
variable (h : Guide b t M K w W k)
include h
lemma sky_book (i:Acres f G): Ember k (fun x=>(carriedAt K b W x) i) (w.C*M):= by
   let L:=ContinuousLinearMap.proj (φ:=fun _:Acres f G=>ℝ) (R:=ℝ) i ∘L stripDawn K W
   have ht:= h.position
   have he : ‖L‖≤w.C:= ContinuousLinearMap.opNorm_le_bound _ (zero_le_one.trans w.witness) (fun v=>
      (norm_le_pi_norm (K.dawn v W) i).trans (h.price.score _))
   exact ⟨L.contDiff.contDiffAt.comp _ ht.1,Seas.paidLinear L ht.1 ht.2 he⟩

-- row book for the precursor vector correction. uses D(root) op paid_t at V field.
def gates (K:Core G S) (b:E→Dir G c)(W:Lines S.ratio.count)(t:ℝ)(i:Seats G c f)(x:E) :=
     t⁻¹*K.F0 (t • b x) i + (K.D (t•b x)).mulVec (carriedAt K b W x) i
lemma packing (i:Seats G c f): Ember k (gates K b W t i) (w.piles G S.ratio.count k M t K.R):=by
   let q(y:Dir G c):= K.F0 y i; let v:= fderiv ℝ q 0
   have hv:= Quire.copied (h.price.hands i) w.rprice h.plate.1 h.position h.plate.2
   have he := h.price.self; let c' := w.C; let F(x:E):=t⁻¹ • Quire.wavelet q (t • b x)
   let L: Dir G c →L[ℝ] ℝ:= (ContinuousLinearMap.proj (φ:=fun _:Seats G c f=>ℝ) (R:=ℝ) i ∘L Streets.pledge (K.D 0) ∘L stripDawn K W) + v
   have hr(a:Dir G c) : L a=(K.D 0).mulVec (K.dawn a W) i+v a:=by change Streets.pledge (K.D 0) (K.dawn a W) i + v a= _; rw [Streets.tagged]; rfl
   have hc:1≤c':= w.witness; have hs : ‖L‖ ≤ c'*Real.exp (-w.α*K.R) := by
      apply ContinuousLinearMap.opNorm_le_bound _ (by positivity); intro a; rw [hr]; exact h.price.tracks ..
   have ht:= h.position.1; have hx:= h.position.2; have hB:= hx.1
   have hf := Ember.join hv (show Ember k (L∘ b) _ from ⟨L.contDiff.contDiffAt.comp _ ht,Seas.paidLinear L ht hx hs⟩)
   let P(j:Acres f G)(x:E):= (K.D (t • b x) i j-K.D 0 i j)*carriedAt K b W x j
   let V(j:Acres f G) := Decay w.α (origin S i) (chair S j)
   let Z:=2^k*w.tone k M t*(c'*M); have hT:=h.plate.1.1; have hQ:= w.tone_ge k hB hT.le; have hZ:0≤Z:=by unfold Z; positivity
   have hV (j) : Ember k (P j) (Z*V j):=by
      have hs:=Ember.fires (h.lintel i j).2.2 (h.sky_book j); rw [show 2^k*(w.tone k M t*V j*(c'*M))=Z*V j from by unfold Z; ring] at hs; exact hs
   let u := fun x:E=>∑ j, P j x
   have hP : ∑ j,Z*V j ≤ Z*(bow G S.ratio.count w.α):= by rw [←Finset.mul_sum]; apply mul_le_mul_of_nonneg_left _ hZ; exact (chair_count G S).count (chair S) w.wisdom _
   have h := Ember.join hf (Ember.weakening (Ember.total _ _ P (fun j _=> hV j)) hP)
   have he':gates K b W t i=(F+(L∘b))+u:=by
      funext x; change _=F x+L (b x)+u x; rw [hr]
      unfold F u P wavelet gates; rw [show q 0=0 from congr_fun he _]; simp only [sub_zero];
      simp_rw [map_smul, smul_sub, inv_smul_smul₀ hT.ne',sub_mul, Finset.sum_sub_distrib]; unfold Matrix.mulVec dotProduct
      unfold v q carriedAt; rw [smul_eq_mul]; abel
   rw [he']; exact h

lemma resumes (i : Acres f G): Ember k (fun x=> (stepped K b t x).mulVec (carriedAt K b W x) i + (patchedAt K b t x) i)
     (w.traps G S.ratio.count k M t K.R):=by
   let V (j:Seats G c f) := Decay w.α (origin S j) (chair S i)
   let F (j:Seats G c f) (x:E) := K.D (t • b x) j i * gates K b W t j x
   let T:= w.piles G S.ratio.count k M t K.R; let Z:=2^k*(2*w.C)*T
   have ht:T≥0:= w.pills _ _ _ _ h.position.2.1 h.plate.1.1.le
   have hh:=w.witness; have hZ : 0≤ Z:= by unfold Z; positivity
   have hf(j): Ember k (F j) (Z*V j):= by
      have he:= Ember.fires (h.lintel j i).2.1 (h.packing j)
      rw [show 2^k*(2*w.C*V j*T)=Z*V j from by unfold Z; ring] at he; exact he
   have he' : (∑ j, Z*V j) ≤ w.traps G S.ratio.count k M t K.R:= by
      rw [←Finset.mul_sum]; unfold V; simp_rw [decay_comm _ _ (chair S i)]
      exact mul_le_mul_of_nonneg_left ((origin_count G S).count (origin S) w.wisdom _) hZ
   apply Ember.renamed (Ember.weakening (Ember.total _ _ F (fun i _=>hf i)) he')
   refine Eventually.of_forall (fun x=>?_)
   let M:= K.D (t • b x); let d:= carriedAt K b W x
   have hP : (stepped K b t x).mulVec d=M.transpose.mulVec (M.mulVec d):= by
      unfold stepped Little.Core.Gram; rw [Matrix.add_mulVec,←Matrix.mulVec_mulVec,K.fires_mul,K.dawn_iced,add_zero]
   dsimp only; rw [show (stepped K b t x).mulVec (carriedAt K b W x) i= M.transpose.mulVec (M.mulVec d) i from congr_fun hP i]
   unfold F gates patchedAt epoxy Matrix.mulVec dotProduct; simp only [Pi.smul_apply,smul_eq_mul,Finset.mul_sum,mul_add,Finset.sum_add_distrib];
   unfold d M; rw [add_comm]; apply congr_arg (·+_); refine Finset.sum_congr rfl (fun j _=>?_); simp only [Matrix.transpose_apply]; ring
end Guide
end YM.Planned.PrimaryIntegral295.Density
