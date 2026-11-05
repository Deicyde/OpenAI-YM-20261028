import YM.OPE.Orbits.Fee
/-! Genuine positive-layer estimates transferred to `Reader` score and homogeneous
physical vectors. Same exterior law throughout, uniform wrt all viewers paths.
Raw-to-old and exact-reader differences are both priced before insertion. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Orbits
open Filter Function Set MeasureTheory Extraction Table Word
open scoped Topology BigOperators ContDiff Classical Matrix.Norms.Frobenius
variable {G:Gauge} {C:Family G}{S:Table C.book}{F:Order}
    (U:Spec.Final C F S) (R:Reader U.sector.derivatives U.sector.turns U.room.kernel.spin)
    (h:Services C F S) {I J L:Type}[Fintype I][Fintype J]{A:L→ℝ}{φ:Filter L}(hA:Tendsto A φ atTop) [φ.NeBot]
    {d:I→ℕ}{e:J→ℕ}{a b c:ℝ}{x:L→I→E4}{y:L→J→E4}{o:L→E4}(v:Labels S d)
local notation "ρ" => U.room.kernel.spin
local notation "Q" => U.sector.derivatives
local notation "P" => R.port
local notation "X" => U.sector.turns
open Reader
variable (hx:enveloped φ A a x o)(hk:Kept φ A a x)(ha:0 < a)
include R h hA hx hk ha
lemma fresh_price (m:ℕ): RateLE φ A (fun i=>R.fresh m (x i) (o i) v) ((weight d-m)*a):=by
   let f (j:Mode Q)(i:L) := ((R.port).ope j (x i) (names v) (o i)) • R.cutTest m m ((R.port).loaded j m)
   let y i:=R.fresh m (x i) (o i) v; let V:=fun i=>∑ j∈bands Q m, f j i
   have h_legacy (i:L):R.cutTest m m (shadowOld P m (x i) (o i) v)= V i:=by simp only [shadowOld,shadow,V,f,map_sum,map_smul]
   have hV: RateLE φ A V ((weight d-m)*a):=RateLE.sum hA (fun j hj=> by
     have hz: j.fst ≤ m:=(full_bands ..).mp hj; rcases lt_or_eq_of_le hz with he|he
     · apply RateLE.congr (F:=fun _:L=>(0:S.Field m)) (RateLE.zero φ A _); refine Eventually.of_forall fun i=>?_ ; unfold f; rw [(R.port).cost j hj,cut_rise R m j.fst m hz, kills_lower R m j.fst he,smul_zero]
     have ha:=available_cost (O:=o) U P (names v) hA h R.spans hx hk ha j; unfold f; rw [weighting v]; exact (ha.smul (RateLE.const (R.cutTest m m (R.port.loaded j m)) hA)).mono (by rw [he,add_zero]))
   have hf:= fresh_bridge (o:=o) (v:=v) U R h hA hx hk ha m m
   refine ((hf.mono (b:=(weight d-m)*a) (by linarith only [ha])).add hV hA).congr (Eventually.of_forall (fun i=>?_)); change y i - R.cutTest m m _+V i=y i; rw [h_legacy,sub_add_cancel]

variable (z:L→Viewers U)(w:Labels S e)
variable (hp:Intervals φ A b (fun l=>sole (o l)) y)(hy:Kept φ A c y)(hb:0≤ b)(hc: b ≤ c)
omit R hx hk ha in
include hy hp hb hc in
lemma upon_cost (j:ℕ)(u:S.Field j): RateLE φ A (fun i=>upon (spectator U (z i)) j (o i) (y i) w u) (j*b+weight e*c):=by
    simp only [upon]; show RateLE φ A (fun i=>whole _ _ _ _ _) _
    simp_rw [whole_observed,weighting w]; rw [show (j:ℝ)=(sigma (names (d:=fun _:Unit=> j) (sole u)):ℝ) from by simp [sigma,Fintype.sum_unique,names]]; apply viewer_cost U h.schedule _ _ hA _ (Kept.sole φ A o b) hy hp hb hc
omit R hx hk ha in
include hy hp hb hc in
lemma upon_field_cost (j:ℕ)(u:L→S.Field j)(t)(hu:RateLE φ A u t): RateLE φ A (fun i=>upon (spectator U (z i)) j (o i) (y i) w (u i)) (t + (j*b+weight e*c)):=by
   let f(i:L):MultilinearMap ℂ (fun _:Unit=> S.Field j) ℂ:=sectionLabels w (moment (spectator U (z i)) (d:=Sum.elim (fun _:Unit=>j) e) (beside (sole (o i)) (y i)))
   have hf(i:L)(q:S.Field j):upon (spectator U (z i)) j (o i) (y i) w q=f i (sole q):=(sectionLabels_apply w (m:=moment (spectator U (z i)) (d:=Sum.elim (fun _:Unit=>j) e) (beside (sole (o i)) (y i))) (sole q)).symm
   apply RateLE.congr (F:=fun i=>f i (sole (u i))) ?_ <| Eventually.of_forall (fun i=>(hf ..).symm); rw [add_comm,show t=∑ _:Unit,t from by simp];
   refine contract (φ:=φ) hA f (fun q=> (upon_cost U h hA z w (o:=o) hp hy hb hc j (q ())).congr ?_) _ _ (fun ()=>hu)
   exact Eventually.of_forall fun i=> Eq.trans (hf i (q ())) (congr_arg (f i) (funext (fun j=>by cases j; rfl)))

omit h hA hx hk ha [φ.NeBot] in
lemma upon_rise {m j:ℕ}(he:j≤ m)(q:S.Field j)(r:Viewers U) (o:E4)(y:J→E4)(w:Labels S e)(hp:Injective (beside (sole o) y)):upon (spectator U r) m o y w ((Q|>.rise he q))=upon (spectator U r) j o y w q:=by
    rw [upon_observe m w (spectate U r) (spectate_respects U r) hp,lowerOne ..,← upon_observe j w (spectate U r) (spectate_respects U r) hp]; exacts [spectate_ready U r,(spectate U r).laws.toSymmetric,hp,spectate_respects U r] -- inspect lowerOne

/-- Scalar tested full difference; includes centered placement of each fresh-vector output. -/
def balance (T:Table C.book)(R:Reader Q X ρ)(m:ℕ)(x:I→E4)(o:E4)(v:Labels S d)(y:J→E4)(w:Labels S e):=whole T x v y w - ∑ j:Fin (m+1), upon T _ o y w (R.fresh j.val x o v)
-- maybe Q X ρ not bound because notation. fix manually

include hy hp hb hc
lemma balance_rate (m:ℕ)(hba:b < a):RateLE φ A (fun i=>balance U (spectator U (z i)) R m (x i) (o i) v (y i) w) (weight d*a-(m+1:ℝ)*(a-b)+weight e*c) :=by
    let q i:= shadowOld P m (x i) (o i) v; let W i:=discrepancy (spectator U (z i)) m (x i) (o i) v (q i) (y i) w
    let L'(j:ℕ)(i:L):S.Field j→ₗ[ℂ] ℂ:=upon (spectator U (z i)) j (o i) (y i) w
    let f (j:Fin (m+1))(i:L):=R.fresh j.val (x i) (o i) v
    let E (j:Fin (m+1)) i:= L' (j.val:ℕ) i (R.cutTest j.val m (q i)- f j i)
    have hid i(hi:Injective (beside (sole (o i)) (y i))): W i+ (∑ j:Fin (m+1), E j i)=balance U (spectator U (z i)) R m (x i) (o i) v (y i) w:=by
        have he: W i=whole (spectator U (z i)) (x i) v (y i) w- L' m i (q i):=rfl
        have hz:L' m i (q i) = ∑ j:Fin (m+1), L' _ i (R.cutTest j.val m (q i)):=by
              have hu:= R.reconstruct m m (le_refl m) (q i); rw [(Q|>.arrival R.continuum.laws.toSymmetric R.lifts)] at hu; apply Eq.trans (congr_arg (L' m i) hu.symm) (by rw [map_sum]; unfold L'; exact Finset.sum_congr rfl (fun j hj=>upon_rise U R _ _ _ _ _ _ hi)) -- rw fails
        rw [he,hz]; unfold balance E; simp_rw [map_sub,Finset.sum_sub_distrib]; change _ = whole _ _ _ _ _ - ∑ j,L' _ i (f j i); abel
    let ξ:= weight d*a-(m+1:ℝ)*(a-b)+weight e*c
    have hx2:= (clearance_both hA hx hk hp hy hba hc).1
    have hf:=discrepancy_rate_old U R h hA z v w hx hk hp hy ha hb hba hc m
    refine (hf.add (RateLE.sum hA (f:=E) (fun j hj=>?_)) hA).congr <| hx2.mono hid
    have h':=(fresh_bridge (v:=v) U R h hA hx hk ha m j.val).neg.congr (Eventually.of_forall fun i=> (neg_sub (f j i) (R.cutTest _ m (q i)))) -- orientation rate neg.congr expects Eq?
    exact (upon_field_cost U h hA z w hp hy hb hc j.val _ _ h').mono (by have hi : (j.val:ℝ) ≤ m+1:=(by exact_mod_cast j.isLt.le); linarith only [mul_le_mul_of_nonneg_right hi hb])
end YM.OPE.Orbits
