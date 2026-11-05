import YM.MergeProof.West.Knight
import YM.Next.RANK.License
import YM.Next.RANK.Pension
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Edition
open Function Filter RG Thirst Lattice Wilson MeasureTheory Relation Corona Value Glyph Marker Perch Vac.Numbers Alarm Spindle Station Cells Atlas Finset Baler Source
open scoped BigOperators Classical Topology Matrix.Norms.Frobenius

variable {G : Gauge} {n : Side} {A : Activities G n} {Q : Rep G n} {V ι κ : Type} [DecidableEq V] [Fintype V]
variable {d : ℕ} {ζ : V→ Site n} {t τ : ℝ} {p q : BudgetPoint} {e u v' : ℝ}

variable {C : Family G} {N k i v p' : ℕ}
variable {d: Fin (v+1)→ℕ}(X : Points (v+1)) (hN : k≤N) (s : ℝ) (A : (i:Fin (v+1))→ C.label (d i))
variable {P': Neat (C.side k p') → Burst G (C.side k p') (C.path.rep N p' k).p.threshold}
variable (h : C.Makes) (hp : ∀ i, C.ref (d i)≤k)
include h hp

lemma farerX {a : ℝ} (B : Neat (C.side k p') → Burst G (C.side k p') (C.path.rep N p' k).p.threshold)
    (he : IsoVac _ B (C.path.levels.clock.forcedAllowance k)) (r : Listens C s (v:=v+1) hN p'→ℝ) (hr : ∀ i,0 ≤r i) {e : ℝ}
    (ha : Lower (C.path.rep N p' k).p q) (hE : 0≤ e) (H' : Spaced (C.path.rep N p' k).p.B (seats C s X hN p'))
    (hZ : scalesExp (C.path.rep N p' k).p q (e+1)) (hh : ∀ i,r i* moneys C (d i.2) k N p' (A i.2) ≤ a) :
    let u:= C.path.levels.clock.forcedAllowance k
    Burden (ensembleOX X hN s A B h hp) q r e (83521*(Real.exp (100000*e)*u)+wilt q.B*(Real.exp (100000*(e+1))*(a*Real.sqrt u))):= by
  intro u
  let P:= C.path.rep N p' k; let ζ:= seats C s X hN p'
  let J := fun i:Fin (v+1)=> pinHat C (d i) k
  let S := fun v : (Listens C s (v:=v+1) hN p') × Rootage (C.side k p')=>
      bitsX ζ (pressX hN s A) (fun i=> satisfiesX hN s A i h hp) (hand C s hN p') (fp C s hN p') (fun j=> J j.2) v.1 v.2
  have hc := injected _ ζ P.p.B_pos H'
  apply sum_token (enroll ζ ∘ B) S
  · obtain ⟨c,H,hQ⟩:=he.smooth; refine ⟨c,fun i=>⟨(H i).1,fun U=>?_⟩,
      ShiftUp (E:=enroll ζ ∘ B) _ _ ha e hE ?_ (fun i=>(H i).1) _ hQ⟩
    · dsimp only [Function.comp_apply,enroll]; simp_rw [Poly.quiet_toll,Complex.norm_real,one_mul]; exact (H _).2 _
    apply le_trans _ hZ; gcongr; linarith only
  choose m hm hz using fun i:Listens C s (v:=v+1) hN p' => show ∃ m : Rootage (C.side k p')→ℝ,(∀ j,heavy (S (i,j)) r (m j)) ∧
    ∑ j,m j* Value.charge P.p P.p.supportExponent (S (i,j)).extent ≤ a*Real.sqrt u from by
    obtain ⟨p,b,h₁,h₂,H,hg⟩:=force_bars hN (h:=h) (hp:=hp i.2) (A i.2) p'
    obtain ⟨m,hp,hX⟩:=root_budget (F:=pressX hN s A i) (hand C s hN p' i) (satisfiesX hN s A i h hp) (fp C s hN p' i) (J i.2) H hg i r (hr i) (ζ:=ζ)
    have hy:0 ≤ Real.sqrt u:= Real.sqrt_nonneg _
    refine ⟨m,hp,hX.trans ?_⟩; have hp:= ((mul_le_mul_of_nonneg_left h₂ (hr _)).trans (hh i)); change r i*‖J i.2‖*(Real.sqrt u*b)≤_
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

namespace YM.Next.Rank.Edition
open Function Filter RG Thirst Lattice Wilson MeasureTheory Relation Corona Value Glyph Marker Perch Vac.Numbers Alarm Spindle Station Cells Atlas Finset Baler Source Labels EntryWord Exponential
open scoped BigOperators Classical Topology Matrix.Norms.Frobenius

variable {G : Gauge} {n : Side} {C : Family G} {ι κ χ μ V : Type} [Fintype V] [DecidableEq V]
variable {N k d p m i : ℕ} {q : BudgetPoint} {ζ : V→Site n} {τ : ℝ}

variable (m i : ℕ){d:Fin (m+1)→ℕ} (Y : Points (m+1)) (b : ℝ) (hN : k≤N) (v : (i:Fin (m+1)) → C.label (d i))
variable {Q : Rep G (C.side k p)} {B : Neat (C.side k p)→Burst G (C.side k p) (C.path.rep N p k).p.threshold}
variable {X : Keepat (C.side k p)} {w : Fin (m+1) → Config G (C.side k p)→ℂ} {c : Fin (m+1)→ℝ}

variable (t : Listens C b (v:=m+1) hN p→ℝ)
variable [Fintype ι]
variable (A : ι → SourceAt G (seats C b Y hN p))
variable (h : C.Makes) (hp : ∀ i, C.ref (d i) ≤ k) (ht : ∀ j,Ticket (v j) i k N p Q.p X (w j) (c j))

lemma ember_costX {ℓ : Q.p.threshold≤ (C.path.rep N p k).p.threshold} (hr : ∀ i,0≤t i) {e z : ℝ} (_ : 0≤e) (hy : ∀ i : Listens C b (v:=m+1) hN p,
    t i*moneys C (d i.2) k N p (v i.2)≤ z) (hs : Injective (seats C b Y hN p)) :
    let E:=readyStrX m i Y b hN v h hp ht ℓ
    taxable (q:=Q.p) E t e (wilt Q.p.B*(3*z * debt Q.p.B (e+1) (halo 8 X.val))) := by
  intro F
  let f:= seats C b Y hN p
  let a x:=3*(t x*moneys C (d x.2) k N p (v x.2)); have ha j : Taxed (F j) (q:=Q.p) t (a j):= hW_damp (v j.2) i h (hp j.2) hN (hand C b hN p j) (fp C b hN p j) j (ht j.2) ℓ t (hr j)
  have hp i:(F i).fires=slot i:=rfl
  let y:=3*z*debt Q.p.B (e+1) (halo 8 X.val)
  have hz : 0 ≤ z:=by
    let c : Listens C b (v:=m+1) hN p := (0,0)
    exact (mul_nonneg (hr c) (money_nn ..)).trans (hy c)
  have H j:debt Q.p.B (e+1) (F j).extent=debt Q.p.B (e+1) (halo 8 X.val):= by
    unfold debt; rw [show (F j).extent=halo 8 (swath (hand C b hN p j) (f j) X.val) from rfl,← swath_iffHalo,swath_cover]
  have ht : stars Q.p (fun i=> (F i).fires) (fun i=> (F i).extent) (e+1) a y:= by
    refine shorten (A:=fun i=>(F i).fires) _ hp (fun x=> ?_) (fun x=> (ha _).1)
    rw [H]; exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hy x) (by norm_num : (0:ℝ)≤3)) (Real.exp_pos _).le
  have hh (i): (F i).fires.val.Nonempty:= by rw [hp];exact singleton_nonempty _
  exact ⟨a,ha,roots_hits _ _ _ hs hh (fun i=> (F i).remembers) (fun i=> (ha i).1) (mul_nonneg (mul_nonneg (by norm_num) hz) (Real.exp_pos _).le) ht⟩

lemma roilX (hr : ∀ i,0 ≤ t i) {e z : ℝ} (hZ : ∀ i,c i≥0) (hx : ∀ i,t i*c i.2 ≤ z):
    Unpacks (readyNearX m i Y b hN v h hp ht) Q.p t e (z * debt Q.p.B e X.val):= by
  let a x:=t x*c x.2;let F:=readyNearX m i Y b hN v h hp ht
  have hh j: transported (F j) Q.p.threshold t (a j):= Rshot_cost (v j.2) i h (hp j.2) hN (hand C b hN p j) (fp C b hN p j) j (ht j.2) t (hr j) (hZ _)
  have hp j:debt Q.p.B e (F j).extent=debt Q.p.B e X.val:=by unfold debt; rw [show _=swath _ _ X.val from (show (F j).extent=swath (hand C b hN p j) (seats C b Y hN p j) X.val from rfl),swath_cover]
  refine ⟨a,hh,shorten (A:=fun i=>(F i).fires) _ (fun i=>rfl) (fun j=>?_) fun i=>(hh i).1⟩
  rw [hp]; exact mul_le_mul_of_nonneg_right (hx _) (Real.exp_pos _).le

-- assembling long routes
lemma cloudsX (hr : ∀ i,0 ≤ t i) {e z : ℝ} (he : 0≤e) {q : BudgetPoint} (H : Lower (C.path.rep N p k).p q)
    (hc : scalesExp (C.path.rep N p k).p q (2*e)) (hy : ∀ i,t i*moneys C (d i.2) k N p (v i.2) ≤ z):
    let A:= C.path.rep N p k
    let F:= readyWideX m i Y b hN v h hp
    Credit F A.p q t e (Real.exp (100000*e)* Real.exp (-(A.p.supportExponent*i)/2) * z):= by
  intro D F
  let P:= D.p
  choose Fz hm Hm using fun j : Listens C b (v:=m+1) hN p => long_cost (ζ:=seats C b Y hN p) i (v j.2) h (hp j.2) hN j (fp C b hN p j) (hand C b hN p j) e (C.path.rep N p k).p rfl H he hc t (hr j)
  let C (v : Listens C b (v:=m+1) hN p × Keepat (C.side k p)):=Fz v.1 v.2
  have hC j:transported (F j) P.threshold t (C j):= hm j.1 j.2
  have he v:(F v).fires=slot v.1:=rfl
  refine ⟨C,hC,fun x=>?_⟩; apply (sum_pay ..).2
  · rw [Fintype.sum_prod_type]; rw [Finset.sum_eq_single x]
    · have hp j:x∈(F (x,j)).fires.val:= mem_singleton_self _
      simp only [hp,↓reduceIte]; exact (Hm x).trans (mul_le_mul_of_nonneg_left (hy x) (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le))
    · intro i hi h; apply sum_eq_zero;intro y _; exact if_neg (fun H=> h (mem_singleton.mp H).symm)
    simp
  exact fun i=> mul_nonneg (hC i|>.1) (Real.exp_pos _).le
end YM.Next.Rank.Edition
