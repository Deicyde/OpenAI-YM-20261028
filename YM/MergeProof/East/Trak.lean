import YM.MergeProof.East.Chore
import YM.Next.RANK.Spirals


/-!
# W polynomial at k supplied before the course

Re-express Taylor at the new threshold on its complete stencil. Take τ actual uses;
log costs in pressure tests still on old unweighted cap. Remainder bound is on every U
on the smaller-threshold footprint, not just on unmarked integral. -/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Spindle
open Function Filter Set RG Source Wilson Extraction Lattice Labels Perch Configuration Atlas Beamer
open Normal Rise Common Filter Glimmer LiftMark Station Asymptotics MvPolynomial
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff Classical

variable {G : Gauge} {C : Family G}
variable {N p k d nD b i : ℕ} {n : Side}

lemma chas_v (S : Rules G) (C : Family G) (c : ℝ) (hc : 0 ≤ c) (d D : ℕ) (Hg : G.Simple) (h : C.Makes) (κ:ℝ) (hκ:0<κ) : ∀ᶠ k in atTop,
    ∀ N,k ≤ N→ ∀ p,
      C.ref d ≤ k → year C D k →
      let b:= sizeQ C k;let A:=C.path.levels; let m:=scouts C k; let s:=clim A k
      let g:= GaugeScale C k N p; let V:= C.path.rep N p k
      ∀ w : C.label d, ∀ P, WRead S k N p d b m D (shadow C k p D c) w P→ ∀ u : Provision C d k N p m b,
        ∀ U : Config G (C.side k p), Healthy (tau A k) (patch b 0) U →
          ‖nearHol C w m k N p U - signet 0 g (sender u.length V.p.threshold g P) U‖ ≤ κ * Perch.bill (-(D:ℝ)) s * paid C d k N p w := by
  let A:= C.path.levels;let e:=α₀ D; have hx : 0<e:= alpha_pos _
  have he:= (show e*((D:ℝ)+2)≤1/16 from αpay D)
  let v:= -(D:ℝ);let K:= v-2-2*e; let J:= hat_rate A Hg
  have hi : e+(-1+e)*((D:ℝ)+1)< v:= by unfold v e at *; linarith only [he]
  have hs : e+e+K < v := by unfold K; linarith only
  filter_upwards [J.eventually (transports' hi (3*(4:ℝ)) hκ),J.eventually (transports' (show K+e < v by linarith only [hs,hx]) 3 hκ),
    J.eventually (transports' hs (3*4*(D:ℝ)) hκ),iced S C Hg h K,radius_paid C hx Hg h, shrank C (-K) Hg h,checks C D c e Hg hx] with k h1 h2 h3 H hr hB hv N hN p hR hW
  intro b A' m s g V w P hp u U hU
  obtain ⟨⟨Ho,Hq,Hf⟩,hK⟩:= H
  let r:= 4*(b:ℝ)*tau A k; let B:= A.clock.threshold k; let M:= Perch.bill e s;let Y:=Perch.bill K s
  have hh : (C.path.rep N p k).p.threshold=B:= by rw [(h.wilson.represents N p k hN).vac];rfl
  have hw:= issued S w u (tau A k) (tau_pos A k) hp h hR hN U hU Ho
  dsimp only at hw; rw [hh] at hw; change V.p.threshold=B at hh
  rw [hh]; apply (hw Hq Hf).trans
  let L:= paid C d k N p w
  have hc' : 0 ≤ shadow C k p D c:= by unfold shadow; positivity
  have hy : 0 ≤ L := paid_pos ..; have hm : 0 ≤ moneys C d k N p w:=money_nn ..; have hM : 0 ≤ M:= (Real.exp_pos _).le
  have ht' : 0≤Y:=(Real.exp_pos _).le; have hb : 0≤B := (A.budget k).threshold_pos.le
  have ha : 0≤r:= mul_nonneg (by positivity) (tau_pos ..).le
  have ht := (show moneys C d k N p w ≤ M*L from mul_le_mul_of_nonneg_right hW hy)
  have hd : (2*r/B)^(D+1) ≤ Perch.bill ((-1+e)*((D:ℝ)+1)) s := by
    refine (pow_le_pow_left₀ (show 0 ≤ 2*r/B by positivity) hr (D+1)).trans_eq ?_; rw [Glimmer.bills]; push_cast;rfl
  have ha' : expCut V.p m ≤ Y := by simpa only [neg_neg] using! hB N hN p
  have hP : coin P ≤ 4*(M*L)* M := (tallied hp hc').2.trans (mul_le_mul (mul_le_mul_of_nonneg_left ht (by norm_num)) (hv p) hc' (by positivity))
  change 4*moneys _ _ _ _ _ _* (2*r/B)^(D+1) + expCut V.p m* _ + coin P * (D*((S.C+G.colorScale)*r^2/B)) ≤ _
  apply (add_le_add (add_le_add (mul_le_mul (mul_le_mul_of_nonneg_left ht (by norm_num)) hd (pow_nonneg (by positivity) _) (by positivity)) (mul_le_mul ha' ht hm ht'))
    (mul_le_mul hP (mul_le_mul_of_nonneg_left hK (Nat.cast_nonneg _)) (by have hc:=S.positive; have hc':= G.colorScale_pos; positivity) (by positivity))).trans
  rw [← overlap] at h1 h2; rw [← overlap,←overlap] at h3; dsimp only [M,L,K,Y,v,A,clim] at *; linarith only [mul_le_mul_of_nonneg_right h1 hy,mul_le_mul_of_nonneg_right h2 hy,mul_le_mul_of_nonneg_right h3 hy]
end YM.Next.Rank.Spindle
