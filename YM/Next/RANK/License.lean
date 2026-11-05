import YM.Next.RANK.SealMix
import YM.Next.RANK.Strat

/-!
# Pay singleton forced onto old k prices
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Edition
open Function Filter RG Thirst Lattice Wilson MeasureTheory Relation Corona Value Glyph Marker Perch Vac.Numbers Alarm Spindle Station Cells Atlas Finset Baler Source
open scoped BigOperators Classical Topology Matrix.Norms.Frobenius

variable {G : Gauge} {n : Side} {A : Activities G n} {Q : Rep G n} {V ι κ : Type} [DecidableEq V] [Fintype V]
variable {d : ℕ} {ζ : V→ Site n} {t τ : ℝ} {p q : BudgetPoint} {e u v' : ℝ}

lemma sum_token [Fintype ι] [Fintype κ] (E : ι→Lifted G ζ t) (F : κ→Lifted G ζ t) (r : V→ℝ) (h : Burden E p r e u) (hp : Burden F p r e v'): Burden (Sum.elim E F) p r e (u+v'):= by
  obtain ⟨m,H,hm⟩:= h; obtain ⟨L,h,hL⟩:=hp
  let X:=Sum.elim m L; let S:=Sum.elim E F
  have hh x: heavy (S x) r (X x):= by cases x with | inl x=>exact H _| inr x=>exact h _
  refine ⟨X,hh,fun j=>?_⟩; let P x:= halo 8 (S x).extent; let f i:= X i*debt p.B e (P i)
  refine (sum_pay (u+v') (fun i=> j∈P i) f (fun i=>mul_nonneg (hh i).1 (posit ..|>.le))).2 ?_
  rw [Fintype.sum_sum_type]; apply add_le_add
  · simpa only [tsum_fintype,X,f,P,S,Sum.elim_inl,pay] using! (hm j).2.2
  simpa only [tsum_fintype,X,f,P,S,Sum.elim_inr,pay] using! (hL j).2.2

variable {C : Family G} {N k i v p' : ℕ}
variable (X : Points (v+1)) (hN : k≤N) (s : ℝ) (A : Fin (v+1) → C.label d)
variable {P': Neat (C.side k p') → Burst G (C.side k p') (C.path.rep N p' k).p.threshold}
variable (h : C.Makes) (hp : C.ref d ≤ k)
include h hp

include hN in
lemma force_bars (v : C.label d) (p : ℕ) :
    let P:= C.path.rep N p k;let V:= parcel C d k N p v;let A:= C.path.levels
    ∃ Y : ℕ→ℝ, ∃ u : ℝ,0≤u ∧ ‖pinHat C d k‖*u ≤ moneys C d k N p v ∧
      (∀ i,0≤Y i∧∀ U, ‖V.forced i U‖≤ Y i) ∧ SumBudget (fun i=> P.p.mass (P.activities.forced i).support (Y i)) (Real.sqrt (A.clock.forcedAllowance k)*u):= by
  intro P V A
  obtain ⟨a,b,hb,hb',hh,-,-,e,hq,hs⟩:=(h.calibrated d N p (hp.trans hN)).cap k hp hN ((C.factory d N p).terminal.symm v)
  refine ⟨e,b,hb',?_,hs,hq⟩
  let F:= C.labels.level d; let c:=(A.params k).columns
  have he : 0≤c:=zero_le_one.trans (A.params k).columns_ge
  have hz : b≤c*F.coeffSize V.x := ((le_add_of_nonneg_left hb).trans hh).trans (mul_le_mul_of_nonneg_left (rotate_core F _) he)
  apply (mul_le_mul_of_nonneg_left hz (norm_nonneg _)).trans_eq; unfold moneys Spindle.paid
  change _=c*(∑ i,‖(pinHat C d k•V.x) i‖)
  simp_rw [Pi.smul_apply,norm_smul, ←Finset.mul_sum]; exact mul_left_comm ..

lemma farer {a : ℝ} (B : Neat (C.side k p') → Burst G (C.side k p') (C.path.rep N p' k).p.threshold)
    (he : IsoVac _ B (C.path.levels.clock.forcedAllowance k)) (r : Listens C s (v:=v+1) hN p'→ℝ) (hr : ∀ i,0 ≤r i) {e : ℝ}
    (ha : Lower (C.path.rep N p' k).p q) (hE : 0≤ e) (H' : Spaced (C.path.rep N p' k).p.B (seats C s X hN p'))
    (hZ : scalesExp (C.path.rep N p' k).p q (e+1)) (hh : ∀ i,r i* moneys C d k N p' (A i.2) ≤ a) :
    let u:= C.path.levels.clock.forcedAllowance k
    Burden (ensembleO X hN s A B h hp) q r e (83521*(Real.exp (100000*e)*u)+wilt q.B*(Real.exp (100000*(e+1))*(a*Real.sqrt u))):= by
  intro u
  let P:= C.path.rep N p' k; let ζ:= seats C s X hN p'
  let J := pinHat C d k
  let S := fun v : (Listens C s (v:=v+1) hN p') × Rootage (C.side k p')=>
      bits ζ (press hN s A) J (fun i=> satisfies hN s A i h hp) (hand C s hN p') (fp C s hN p') v.1 v.2
  have hc := injected _ ζ P.p.B_pos H'
  apply sum_token (enroll ζ ∘ B) S
  · obtain ⟨c,H,hQ⟩:=he.smooth; refine ⟨c,fun i=>⟨(H i).1,fun U=>?_⟩,
      ShiftUp (E:=enroll ζ ∘ B) _ _ ha e hE ?_ (fun i=>(H i).1) _ hQ⟩
    · dsimp only [Function.comp_apply,enroll]; simp_rw [Poly.quiet_toll,Complex.norm_real,one_mul]; exact (H _).2 _
    apply le_trans _ hZ; gcongr; linarith only
  choose m hm hz using fun i:Listens C s (v:=v+1) hN p' => show ∃ m : Rootage (C.side k p')→ℝ,(∀ j,heavy (S (i,j)) r (m j)) ∧
    ∑ j,m j* Value.charge P.p P.p.supportExponent (S (i,j)).extent ≤ a*Real.sqrt u from by
    obtain ⟨p,b,h₁,h₂,H,hg⟩:=force_bars hN (h:=h) (hp:=hp) (A i.2) p'
    obtain ⟨m,hp,hX⟩:=root_budget (F:=press hN s A i) (hand C s hN p' i) (satisfies hN s A i h hp) (fp C s hN p' i) J H hg i r (hr i) (ζ:=ζ)
    have hy:0 ≤ Real.sqrt u:= Real.sqrt_nonneg _
    refine ⟨m,hp,hX.trans ?_⟩; have hp:= ((mul_le_mul_of_nonneg_left h₂ (hr _)).trans (hh i)); change r i*‖J‖*(Real.sqrt u*b)≤_
    linarith only [mul_le_mul_of_nonneg_right hp hy]
  let Cw (j : (Listens C s (v:=v+1) hN p') × Rootage (C.side k p')):=m j.1 j.2
  have ht j: heavy (S j) r (Cw j):= hm j.1 j.2; let F j:= (S j).fires; let Z i:= halo 8 (S i).extent
  have hF i : (S i).fires=slot i.1:=rfl
  have ht' : 0≤a := by
    let x:Listens C s (v:=v+1) hN p':=(0,0); exact le_trans (mul_nonneg (hr x) (money_nn ..)) (hh x)
  refine ⟨Cw,ht,roots_hits Z F ζ hc (fun i=> by unfold F;rw [hF];exact singleton_nonempty _) (fun i j hj=> halo_subset _ _ ((S i).remembers j hj))
    (fun i=> (ht i).1) (by positivity) ?_⟩
  intro x; let f j:= Cw j*debt q.B (e+1) (Z j)
  apply (sum_pay _ (fun i=> x∈(F i).val) f (fun i=>mul_nonneg (ht i).1 (Real.exp_pos _).le)).2
  rw [Fintype.sum_prod_type]; rw [Finset.sum_eq_single x]
  · apply le_trans _ (mul_le_mul_of_nonneg_left (hz x) (Real.exp_pos _).le); rw [Finset.mul_sum]; apply sum_le_sum; intro i _
    rw [if_pos (show x∈ (F (x,i)).val from mem_singleton_self _)]; apply (mul_le_mul_of_nonneg_left (scaler P.p q ha hZ (add_nonneg hE zero_le_one) (S (x,i)).extent) (hm x i|>.1)).trans_eq
    exact mul_left_comm ..
  · intro i _ hi; apply sum_eq_zero; intro j _; exact if_neg (fun h=> hi (mem_singleton.mp h).symm)
  simp
end YM.Next.Rank.Edition
