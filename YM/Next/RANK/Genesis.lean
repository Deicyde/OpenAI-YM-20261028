import YM.Next.RANK.Fleet
import YM.Next.RANK.Stepped


/-!
# Candle k output

Starting calendar allowed level and exact course from N. From post-L costs on
THIS stage get full unmarked restarted representation without losing coupling or
scalar and operands needed for marker continuation. -/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Paint
open Function Filter RG Thirst Lattice Wilson MeasureTheory Relation Corona Value Glyph Marker Perch Vac.Numbers Alarm
open scoped BigOperators Classical Topology Matrix.Norms.Frobenius

variable {G : Gauge} {N a m k : ℕ} (C : Family G)
variable {o v u x : ℝ}

structure Ready (v u s x : ℝ) (A : Stage) : Prop where
  provision : Winter (G:=G) A v u s x
  allowance : delta s ≤ 1
  gain : 4≤hot s
lemma offering (S : Stage) (v u x : ℝ) (hv : S.supportExponent ≤ v) (h : 0<u) (hp : u≤ S.clip.linear/20) : ∀ᶠ s in atTop, Ready (G:=G) v u s x S:= by
  filter_upwards [stage_fires S v u x hv h hp, timeLoan (11/5) (by norm_num) 0,surge.eventually_ge_atTop 4] with s hs hg hp
  exact ⟨hs,le_trans (le_abs_self _) (hg.trans (by simp [bill])),hp⟩

lemma historic (L : Levels G) (k): L.clock.threshold k= regular (L.clock.hatBeta k) ∧ (L.budget k).B=M (L.clock.hatBeta k) ∧
    L.clock.monitor k=bill 1 (L.clock.hatBeta k) := by
  have ht : L.clock.monitor k=bill 1 (L.clock.hatBeta k):=by simp [bill,Calendar.monitor,boil,y]
  refine ⟨?_,rfl,ht⟩; unfold Calendar.threshold; rw [ht];rfl

def TableReady (k : ℕ) (x v u : ℝ):= Ready (G:=G) v u (C.path.levels.clock.hatBeta k) x (C.path.levels.params k)

def inbox (k : ℕ) (h : TableReady C k x v u) : BudgetPoint :=
    let s:= C.path.levels.clock.hatBeta k; let b:=C.path.levels.budget k
    { b with
      B := walls s
      threshold := phase s
      B_pos := lt_of_lt_of_le (show 0<M s from b.B_pos) h.provision.2.2.2.1
      threshold_pos := alpha_phase s h.provision.1
      threshold_le := (by
        have hh:regular s ≤1:=h.provision.2.1
        exact le_trans (show phase s≤regular s by nlinarith only [show 2*phase s≤ regular s from h.provision.2.2.1,alpha_phase s h.provision.1]) hh) }
lemma inbox_hot (hN : k≤N) (h : C.Makes) (p : ℕ) (hp : TableReady C k x v u) : Lower (C.path.rep N p k).p (inbox C k hp):= by
  rw [(h.wilson.represents N p k hN).vac]; refine ⟨hp.provision.2.2.2.1,rfl,rfl,rfl,?_,hp.provision.2.2.2.2.1⟩
  let A:= C.path.levels
  rw [show (A.budget k).threshold= _ from (show (A.budget k).threshold=regular (A.clock.hatBeta k) from (historic A k).1)]; exact hp.provision.2.2.1

def survivors (N k p : ℕ) (hp : TableReady C k x v u) (P : Rep G (C.side k p)) :=
    let A:= C.path.levels; let H:= C.path.rep N p k; let q:= inbox C k hp; let j:=A.params k
    let s:=A.clock.hatBeta k; let b:=trib u s; let f:=A.clock;let Λ:=f.loopCap k;let δ:= delta s
    P.eval= H.eval ∧ P.Lawful j.width j.paths Λ δ (Real.exp (-b)) ∧ ∃ X W,
      Bridges (q:=q) H P v b j.width j.paths Λ δ X W ∧ Drama H.path H.activities H.clip H.beta δ v (forcing s) j.width j.paths Λ H.p q b ∧
        vacancies v Λ j.width j.paths δ P.beta H.p q≤bill x s ∧ plane (forcing s) v ≤bill x s ∧ batch b (v+1) q.B ≤bill x s

lemma parser (hN : k≤N) (h : C.Makes) (hp : TableReady C k x v u) (p : ℕ): ∃ Q,survivors C N k p hp Q:= by
  let A:= C.path.levels; let K:= C.path.rep N p k; let s:= A.clock.hatBeta k
  let R:= A.params k; let f:= A.clock;let b:= inbox C k hp
  let H:= h.wilson.represents N p k hN
  have hx : K.p=A.budget k:= H.vac
  obtain ⟨h1,h2,h3⟩:= historic A k
  have ht:Lower K.p b:=inbox_hot C hN h p hp
  have hu : f.theta (f.J k) ≤1:= by
    apply (A.fits.thetaRange k).2.trans; have hz : 1≤ (A.clock.J k:ℝ) := by exact_mod_cast (le_trans (by decide) (A.clock.adm k) : 1 ≤ A.clock.J k)
    exact (inv_anti₀ zero_lt_one hz).trans (inv_one.le)
  have hl := hp.provision.2.2.2.2.2.2 _ hu K.p (hx ▸ h2) (hx ▸ h1) (hx ▸ rfl) b rfl rfl ht ht.still K.beta H.band.1 H.band.2 _ K.path K.activities
  have hv : K.clip = (A.params k).clip:= H.clip
  let L:=2*bill 1 s^f.theta (f.J k)
  have hh:f.loopCap k=L := by unfold Calendar.loopCap; rw [show f.monitor k= _ from h3]
  have hf : f.forcedAllowance k=forcing s:= by unfold Calendar.forcedAllowance; rw [show f.monitor k= _ from h3]; rfl
  have hd : Drama K.path K.activities K.clip K.beta (f.allowance k) v (f.forcedAllowance k) R.width R.paths (f.loopCap k) K.p b (trib u s):= by rw [hh,hv,hf]; exact hl.1
  have ha := Overlay.beta_positive h.wilson (p:=p) hN
  obtain ⟨X,W,Q,H₁,H₂,H₃⟩:= reductions H.good ha.le hd
  refine ⟨Q,H₂,H₃,X,W,H₁,(show Drama _ _ _ _ _ _ _ _ _ _ _ _ _ from hf ▸ hd),?_,hl.2.2⟩
  change vacancies v (f.loopCap k) _ _ _ _ _ _≤ _; rw [H₁.precise.2.2.2.2.2.1,hh]; exact hl.2.1

lemma lights {p} (hN : k≤N) (T : Course C N p k) (h : C.Makes) (hp : TableReady C k x v u) (Q) (H : survivors C N k p hp Q) : Candle T k Q hN:= by
  let A:=C.path.levels; let V:= C.path.rep N p k; let f:=A.clock;let s:= f.hatBeta k; let a:= A.params k
  obtain ⟨hs,hv,X,W,Y,H₀,He⟩:=H
  have hb : Q.p= inbox C k hp := Y.precise.2.2.2.2.1
  have hz : Q.beta= V.beta:= Y.precise.2.2.2.2.2.1
  let g:= (Real.sqrt Q.beta)⁻¹
  have hh:= h.wilson.represents N p k hN
  have hy : Q.clip=a.clip:= Y.precise.2.1.trans hh.clip
  have hl : s/2≤ Q.beta:= hz.symm ▸ hh.band.1
  have hw : 0<s:=hp.provision.1
  have ht : Q.beta≤2*s:= hz.symm ▸ hh.band.2
  have hf:0<Q.beta:= lt_of_lt_of_le (div_pos hw (by norm_num)) hl
  have hg:0<g:= by unfold g; positivity
  have hi : Q.beta*g^2=1:= by unfold g; rw [inv_pow, Real.sq_sqrt hf.le,mul_inv_cancel₀ hf.ne']
  have hu:Q.p.threshold=phase s:= hb ▸ rfl
  refine ⟨⟨⟨by rw [hs]; exact T.vacuum_at h k hN le_rfl,(T.same _ le_rfl hN).trans hz.symm⟩,
      a.width,g,f.loopCap k,delta s, Real.exp (-trib u s), ⟨hy,by linarith [show s=A.clock.hatBeta k from rfl],hi,hg,?_,?_,hp.allowance,le_rfl⟩,hv⟩,hb ▸ rfl,hu⟩
  · rw [hu]; have he:0<Hat s:= by rw [logged _ hw]; positivity
    have hk : 4≤ hot s:= hp.gain
    have hv' : s*Hat s ^2=1:=by unfold Hat;rw [inv_pow,Real.sq_sqrt hw.le,mul_inv_cancel₀ hw.ne']
    change g≤Hat s *hot s
    apply le_trans (b:=Hat s * 2)
    · nlinarith [mul_le_mul_of_nonneg_right hl (sq_nonneg (g:ℝ))]
    gcongr; linarith only [hk]
  apply (le_trans ?_ (historic A k).1.ge); rw [hu]; nlinarith only [show 2*phase s≤ regular s from hp.provision.2.2.1,alpha_phase s hw]
end YM.Next.Rank.Paint
