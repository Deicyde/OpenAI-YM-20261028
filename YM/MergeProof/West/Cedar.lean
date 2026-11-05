import YM.MergeProof.West.Nines
import YM.Next.RANK.Ever
import YM.Next.RANK.Genesis

set_option autoImplicit false
set_option synthInstance.maxSize 512
noncomputable section
namespace YM.Next.Rank.Edition
open Function Filter RG Thirst Lattice Wilson MeasureTheory Relation Corona Value Glyph Marker Perch Vac.Numbers Alarm Spindle Station Cells Atlas Finset Baler Source Labels EntryWord Exponential
open scoped BigOperators Classical Topology Matrix.Norms.Frobenius

variable {G : Gauge} {n : Side} {C : Family G} {ι κ χ μ V : Type}
variable {N k d p m i : ℕ} {q : BudgetPoint}

variable (m i : ℕ){d:Fin (m+1)→ℕ} (Y : Points (m+1)) (b : ℝ) (hN : k≤N) (v : (i:Fin (m+1))→ C.label (d i))
variable {Q : Rep G (C.side k p)} {X : Keepat (C.side k p)} {w : Fin (m+1) → Config G (C.side k p)→ℂ} {c : Fin (m+1)→ℝ}
variable (h : C.Makes) (hp : ∀ i,C.ref (d i)≤k) (ht : ∀ j,Ticket (v j) i k N p Q.p X (w j) (c j)) (F : Course C N p k)

-- blank checks must hold from calibrated stage construction

def RodX (Q : Rep G (C.side k p)) (W : Listens C b (v:=m+1) hN p→ SourceAt G (seats C b Y hN p)) (e r w K : ℝ) := ∃ (ι κ : Type), ∃ (_ : Fintype ι) (_ : Fintype κ),
    ∃ (H : ι→ SourceAt G (seats C b Y hN p)) (Y' : κ→Lifted G (seats C b Y hN p) Q.p.threshold),
      BillsX C b Y hN p v F=dust Q (Sum.elim H W) Y' ∧ Background Q Y' ∧ Unpacks H Q.p (fun _=>r) e w ∧ Alarm.prepared (q:=Q.p) Y' (fun _=>r) e K

lemma deliveredX (hV : Spaced (C.path.rep N p k).p.B (seats C b Y hN p))
    (X' : Siren G (C.side k p) Q.p.threshold) (W : ValidX _ → Wickless G _ Q.p.threshold) {r a e z β σ Λ d' c' δ w' γ : ℝ}
    (ℓ : Lower (C.path.rep N p k).p Q.p) (hu : 0<a) (hz : 0≤z) (he : 0≤e) (hr : 0<r) (hy : 0≤ w') (hs : 0≤d')
    (H : BudgetMix (C.path.rep N p k).p Q.p r a (e+2) γ) (hW : ∀ j, 0≤c j) (hH : scalesExp (C.path.rep N p k).p Q.p (2*(e+2)))
    (J : StakeX m Y b hN v h hp F r)
    (hB : Bridges (C.path.rep N p k) Q e z σ β Λ δ X' W (q:=Q.p))
    (hT : ∀ j,a*moneys C (d j) k N p (v j) ≤ w') (hx : ∀ j,a*c j ≤ c')
    (hQ : 2*vacancies e Λ σ β δ (C.path.β N p k) (C.path.rep N p k).p Q.p + strand X.val i (C.path.rep N p k).p Q.p w' e γ +
      mech (C.path.levels.clock.forcedAllowance k) Q.p w' e γ +batch z (e+1) Q.p.B ≤ d')
    (hA : (↑((Q.p.B+Q.p.B+1)^4:ℕ):ℝ)*d' ≤ 1) :
      RodX m Y b hN v F Q (readyHX m i Y b hN v ht) e a (c'*debt Q.p.B e X.val + drain i (C.path.rep N p k).p Q.p w' e γ) (Real.exp (-z)*(Real.exp d'-1)):= by
  let P:= C.path.rep N p k; let t:=fun _ : Listens C b (v:=m+1) hN p=> a; let QW:=wilt Q.p.B
  let Cw:=readyHX m i Y b hN v ht
  obtain ⟨B,h1,ι,κ,hi,hk,A,L,hL,hM,hP,hR,hV'⟩:=J
  let Xw := readyWideX m i Y b hN v h hp (p:=p)
  let G':= Sum.elim A Xw; let Y':=Sum.elim (ensembleOX Y hN b v B h hp) L
  let U := drain i P.p Q.p w' e γ; have H' : 0 ≤ U:= by unfold U drain; positivity
  have hE : (e+1)+1=e+2:=by ring
  have hc:Credit G' P.p Q.p t (e+2) U:= by
    have ht := Credit.mix (transfer _ hL hP H hr hu hV) (cloudsX m i Y b hN v t h hp (fun _=> hu.le) (show 0 ≤e+2 by linarith) ℓ hH (fun i=>hT _))
    apply Credit.relax ht; unfold U drain P; simp
  have hX : scalesExp P.p Q.p (e+1+1) := by apply le_trans _ hH; gcongr; linarith only [he]
  let P1:=standX m i Y b hN v A h hp ht ℓ.good
  let s2:=strand X.val i P.p Q.p w' e γ
  let s3:=mech (C.path.levels.clock.forcedAllowance k) Q.p w' e γ
  have hip:= injected P.p.B _ P.p.B_pos hV
  have hv' : taxable (q:=Q.p) P1 t (e+1) s2 := by
    have hh:=dash_credit P.p Q.p (show Credit G' P.p Q.p t (e+1+1) U from hE.symm ▸ hc) ℓ.good hip H'
    have hz:= ember_costX m i Y b hN v t h hp ht (fun j=> hu.le) (add_nonneg he zero_le_one) (fun j=> hT j.2) hip (ℓ:=ℓ.good)
    apply Edition.taxable.relax (Edition.taxable.add hz hh); rw [hE]; exact le_rfl
  have hY : Burden Y' Q.p t (e+1) s3:= by
    have hs:= farerX Y hN b v h hp B h1 t (fun _=> hu.le) ℓ (add_nonneg he zero_le_one) hV hX (fun i=>hT i.2)
    have hk:= rooted_interest hM hR (show BudgetMix P.p Q.p r a (e+1+1) γ from hE.symm ▸ H) hr hu (add_nonneg he zero_le_one) zero_le_one hV
    apply Edition.Burden.up Q.p (sum_token _ _ _ hs hk); rw [hE]; exact le_rfl
  let K:=teat Y' (Sum.elim (fun i=> (W i).credit (seats C b Y hN p)) P1) X'
  refine ⟨_,_,inferInstance,inferInstance, restedX m i Y b hN v A h hp ht,K,?_,?_,?_,?_⟩
  · rw [← hV'];
    exact funext fun U=> assembledX m i Y b hN v A L h hp ht X' W ℓ.good hB U
  · let V':=Sum.elim (fun i=> (W i).credit (seats C b Y hN p)) (standX m i Y b hN v A h hp ht ℓ.good)
    let E:Y' = Sum.elim (ensembleOX Y hN b v B h hp) L:=rfl
    have he : Nonempty (Germs B W Y' V') := by
      refine ⟨⟨⟨fun i=> .inl (.inl i),fun x y h=> Sum.inl.inj (Sum.inl.inj h)⟩,⟨.inl,fun _ _ h=>Sum.inl.inj h⟩,fun _=>rfl,fun _=>rfl,?_,?_⟩⟩
      · rintro ((x|x)|x) H
        · exact ⟨x,rfl⟩
        · have hQ:slot x.1=quiet _:=H
          obtain ⟨a,ha⟩:= (singleton_nonempty x.1); exact False.elim (notMem_empty a (show a∈(quiet _).val from hQ ▸ (show a∈(slot x.1).val from ha)))
        have ht:= hR x; change (L x).fires= _ at H; rw [H] at ht; change 2 ≤ (∅: Finset _).card at ht; rw [card_empty] at ht; omega
      rintro (x|x) H
      · exact ⟨x,rfl⟩
      have ht':= standModeX m i Y b hN v A h hp ht ℓ.good x
      change (standX m i Y b hN v A h hp ht ℓ.good x).fires=_ at H; rw [H] at ht'; exact False.elim (not_nonempty_empty ht')
    obtain ⟨E⟩:=he; exact fun j U=> (Germs.background X' E j U).trans (hB.jacket B h1.points h1.value j U)
  · apply Unpacks.mix (roilX m i Y b hN v t h hp ht (fun i=> hu.le) hW (fun i=> hx i.2))
    exact Credit.spill t hc ℓ.good (by linarith only) he
  exact Alarm.rarity Y' _ X' (fun i=> hu) (Edition.taxable.add (Alarm.salary _ hB.remain t) hv') hY hB.head hA hQ he hz hs
end YM.Next.Rank.Edition

namespace YM.Next.Rank.Paint
open Function Filter RG Thirst Baler Lattice Wilson MeasureTheory Relation Corona Value Glyph Marker Perch Vac.Numbers Alarm Station Cells Spindle Atlas Edition
open scoped BigOperators Classical Topology Matrix.Norms.Frobenius

variable {G : Gauge} {C : Family G} {N k d p : ℕ}
variable (h : C.Makes) (hN : k≤N)
variable {x v u D y b f E δ : ℝ}

lemma RodX.increase {m : ℕ}{d:Fin (m+1)→ℕ} (Y : Points (m+1)) (s) (t : (i:Fin (m+1))→ C.label (d i)) (c : Course C N p k) {Q M v r a w} (h : RodX m Y s hN t c Q M v r a w)
    {z y : ℝ} (ha : a ≤ z) (hp : w ≤ y): RodX m Y s hN t c Q M v r z y := by
  obtain ⟨α,β,u,f,P,Y,hp',HB,H, B,h,hX⟩:=h
  exact ⟨α,β,u,f,P,Y,hp',HB,H.relax ha,B,h,fun i=>⟨(hX i).1,(hX i).2.1,(hX i).2.2.trans hp⟩⟩

lemma admitsX (hp : TableReady C k x v u) {Q : Rep G (C.side k p)} (V : survivors C N k p hp Q) (m l l' G' : ℕ){d:Fin (m+1)→ℕ}(hk:∀ i,C.ref (d i) ≤ k) (Y : Points (m+1)) (t : (i:Fin (m+1))→ C.label (d i))
    (T : Course C N p k) (Y' : Rocket y v x u l G' l' b (clim C.path.levels k) (C.path.levels.params k))
    (W : Fin (m+1) → Config G (C.side k p) → ℂ) (s : ℝ) :
    let c:= clim C.path.levels k; let r:= bill y c; let i:=M c; let f :=bill (-8) c
    let B : Keepat _:= ⟨halo (G'*Q.p.B) {0}, halo_spec.mpr ⟨0,by simp,by simp⟩⟩
    let η j:=bill (-(l':ℝ)) c*Spindle.paid C (d j) k N p (t j)
    (Spaced (M c) (seats C s Y hN p))→ (∀ j,r* moneys C (d j) k N p (t j) ≤ f) → (J : ∀ j,Ticket (t j) i k N p Q.p B (W j) (η j)) →
      StakeX m Y s hN t h hk T (Hat c^b) → RodX m Y s hN t T Q (readyHX m i Y s hN t J) v r (bill (-(l:ℝ)) c) (Real.exp (-trib u c)):= by
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
  apply RodX.increase hN Y s t T _ hq
  · apply mul_le_of_le_one_right (Real.exp_pos _).le hv
  apply Edition.deliveredX m i Y s hN t h hk J T (hz.symm ▸ he) X' Z hB hf hU (p'.exponent_pos.le.trans hV.wide) (Real.rpow_pos_of_pos h'p _) (Real.exp_pos _).le
    (Real.exp_pos _).le R (fun j=>mul_nonneg (Real.exp_pos _).le (paid_pos ..)) hξ hi hI hm _ _ heT
  · intro j
    have hb:= hm j; let w:= paid C (d j) k N p (t j)
    have hz : r*w≤ f:= le_trans (mul_le_mul_of_nonneg_left (le_mul_of_one_le_left (paid_pos ..) (C.path.levels.params k).columns_ge) hf.le) (hm j)
    change r*(bill _ _ *w) ≤ bill _ _; rw [mul_left_comm]; apply (mul_le_mul_of_nonneg_left hz (Real.exp_pos _).le).trans_eq; exact (overlap ..).trans rfl
  · have hw : V.forcedAllowance k=forcing c:= by unfold Calendar.forcedAllowance; rw [(historic P k).2.2];rfl
    rw [show P.clock.forcedAllowance k=forcing c from hw]; refine le_trans ?_ htQ
    apply add_le_add <;> try exact le_refl _
    apply add_le_add <;> try exact le_refl _
    apply add_le_add <;> try exact le_refl _
    exact mul_le_mul_of_nonneg_left (by rw [hP]; rw [hβ] at h₀; exact h₀) (by positivity)
end YM.Next.Rank.Paint
