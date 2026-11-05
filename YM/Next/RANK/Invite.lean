import YM.Next.RANK.Ever
import YM.Next.RANK.Genesis

/-!
# At every purchased post-L stamp, the priced initial uncorrected array

Port for beginning the W and R iteration. Uses Stake on same label
path (see Starring). -/
set_option autoImplicit false
set_option synthInstance.maxSize 512
noncomputable section
namespace YM.Next.Rank.Paint
open Function Filter RG Thirst Baler Lattice Wilson MeasureTheory Relation Corona Value Glyph Marker Perch Vac.Numbers Alarm Station Cells Spindle Atlas Edition
open scoped BigOperators Classical Topology Matrix.Norms.Frobenius

variable {G : Gauge} {C : Family G} {N k d p : ℕ}
variable (h : C.Makes) (hk : C.ref d≤k) (hN : k≤N)
variable {x v u D y b f E δ : ℝ}

lemma Rod.increase {m : ℕ} (Y : Points (m+1)) (s) (t : Fin (m+1) → C.label d) (c : Course C N p k) {Q M v r a w} (h : Rod m Y s hN t c Q M v r a w)
    {z y : ℝ} (ha : a ≤ z) (hp : w ≤ y): Rod m Y s hN t c Q M v r z y := by
  obtain ⟨α,β,u,f,P,Y,hp',HB,H, B,h,hX⟩:=h
  exact ⟨α,β,u,f,P,Y,hp',HB,H.relax ha,B,h,fun i=>⟨(hX i).1,(hX i).2.1,(hX i).2.2.trans hp⟩⟩

lemma admits (hp : TableReady C k x v u) {Q : Rep G (C.side k p)} (V : survivors C N k p hp Q) (m l l' G' : ℕ) (Y : Points (m+1)) (t : Fin (m+1) → C.label d)
    (T : Course C N p k) (Y' : Rocket y v x u l G' l' b (clim C.path.levels k) (C.path.levels.params k))
    (W : Fin (m+1) → Config G (C.side k p) → ℂ) (s : ℝ) :
    let c:= clim C.path.levels k; let r:= bill y c; let i:=M c; let f :=bill (-8) c
    let B : Keepat _:= ⟨halo (G'*Q.p.B) {0}, halo_spec.mpr ⟨0,by simp,by simp⟩⟩
    let η j:=bill (-(l':ℝ)) c*Spindle.paid C d k N p (t j)
    (Spaced (M c) (seats C s Y hN p))→ (∀ j,r* moneys C d k N p (t j) ≤ f) → (J : ∀ j,Ticket (t j) i k N p Q.p B (W j) (η j)) →
      Stake m Y s hN t h hk T (Hat c^b) → Rod m Y s hN t T Q (readyH m i Y s hN t J) v r (bill (-(l:ℝ)) c) (Real.exp (-trib u c)):= by
  intro c r i f B η he hm J hi; let A:= C.path.rep N p k
  obtain ⟨W,Hv,X,G,hχ,hV,h₀,h1,h₂⟩:=V
  have hh := hχ.precise; let p':= inbox C k hp; have hP : Q.p=p':= hh.2.2.2.2.1
  have ha : A.p=C.path.levels.budget k:= (h.wilson.represents N p k hN).vac
  have hβ : Q.beta = A.beta:=hh.2.2.2.2.2.1
  have hT: (Q.p).B = walls c := hP ▸ rfl
  let P:= C.path.levels
  let V:= P.clock
  have ht:A.p.threshold= regular c:=ha▸ (historic P k).1
  have hz : A.p.B=M c:=ha▸rfl
  have hB :Lower A.p Q.p:=hP ▸ hV.squeeze.1
  obtain ⟨⟨R⟩,hξ,hR⟩:=Y'.2 _ _ hz hT ht (ha ▸ rfl) hB
  let u':=trib u c; have hU : 0 ≤ u':=hV.cost
  have heq : Q.p.threshold=p'.threshold := congr_arg _ hP
  -- transfer certificates cast at same p
  have h' : ∃ X' G', Bridges (q:=Q.p) A Q v u' (P.params k).width (P.params k).paths (V.loopCap k) (delta c) X' G':= by rw [hP]; exact ⟨X,G,hχ⟩
  obtain ⟨X',Z,hI⟩:=h'
  obtain ⟨hq,htQ,heT,hv⟩:= hR _ B rfl
  have hf: 0 < r:= Real.exp_pos _
  have hp':0<c:=hp.provision.1
  have h'p:0< Hat c:= by rw [logged _ hp'];positivity
  apply Rod.increase hN Y s t T _ hq
  · apply mul_le_of_le_one_right (Real.exp_pos _).le hv
  apply Edition.delivered m i Y s hN t h hk J T (hz.symm ▸ he) X' Z hB hf hU (p'.exponent_pos.le.trans hV.wide) (Real.rpow_pos_of_pos h'p _) (Real.exp_pos _).le
    (Real.exp_pos _).le R (fun j=>mul_nonneg (Real.exp_pos _).le (paid_pos ..)) hξ hi hI hm _ _ heT
  · intro j
    have hb:= hm j; let w:= paid C d k N p (t j)
    have hz : r*w≤ f:= le_trans (mul_le_mul_of_nonneg_left (le_mul_of_one_le_left (paid_pos ..) (C.path.levels.params k).columns_ge) hf.le) (hm j)
    change r*(bill _ _ *w) ≤ bill _ _; rw [mul_left_comm]; apply (mul_le_mul_of_nonneg_left hz (Real.exp_pos _).le).trans_eq; exact (overlap ..).trans rfl
  · have hw : V.forcedAllowance k=forcing c:= by unfold Calendar.forcedAllowance; rw [(historic P k).2.2];rfl
    rw [show P.clock.forcedAllowance k=forcing c from hw]; refine le_trans ?_ htQ
    apply add_le_add <;> try exact le_refl _
    apply add_le_add <;> try exact le_refl _
    apply add_le_add <;> try exact le_refl _
    exact mul_le_mul_of_nonneg_left (by rw [hP]; rw [hβ] at h₀; exact h₀) (by positivity)
end YM.Next.Rank.Paint
