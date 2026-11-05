import YM.Next.RANK.ParcelW

/-!
# Initial rights after moving to Q0

Ask entropy fee for R/canon & support even through halo movement. Hitting
P.B antecedents only through counted costs. -/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Edition
open Function Filter RG Thirst Lattice Wilson MeasureTheory Relation Corona Value Glyph Marker Perch Vac.Numbers Alarm Spindle Station Cells Atlas Finset Baler Source Labels EntryWord Exponential
open scoped BigOperators Classical Topology Matrix.Norms.Frobenius

variable {G : Gauge} {n : Side} {C : Family G} {ι κ χ μ V : Type} [Fintype V] [DecidableEq V]
variable {N k d p m i : ℕ} {q : BudgetPoint} {ζ : V→Site n} {τ : ℝ}

lemma shorten {A : V → modes V} (X : V→Support n) {c : V → ℝ} {q : BudgetPoint} {e w : ℝ} (h : ∀ i,A i=slot i) (hp : ∀ i,c i * debt q.B e (X i) ≤ w) (ht : ∀ i,0≤c i): stars q A X e c w:= by
  intro x; apply (sum_pay w _ (fun i=> c i*debt q.B e (X i)) _).2
  · rw [sum_eq_single x]
    · rw [if_pos (show x∈(A x).val by rw [h];exact mem_singleton_self _)]; exact hp x
    · intro b _ hb; exact if_neg (fun he=> hb (Eq.symm (Finset.mem_singleton.mp (show x∈{b} from h b▸ he))))
    simp
  exact fun i=>mul_nonneg (ht i) (Real.exp_pos _).le

variable (m i : ℕ) (Y : Points (m+1)) (b : ℝ) (hN : k≤N) (v : Fin (m+1)→C.label d)
variable {Q : Rep G (C.side k p)} {B : Neat (C.side k p)→Burst G (C.side k p) (C.path.rep N p k).p.threshold}
variable {X : Keepat (C.side k p)} {w : Fin (m+1) → Config G (C.side k p)→ℂ} {c : Fin (m+1)→ℝ}

variable (t : Listens C b (v:=m+1) hN p→ℝ)
variable [Fintype ι]
variable (A : ι → SourceAt G (seats C b Y hN p))
variable (h : C.Makes) (hp : C.ref d≤k) (ht : ∀ j,Ticket (v j) i k N p Q.p X (w j) (c j))

lemma ember_cost {ℓ : Q.p.threshold≤ (C.path.rep N p k).p.threshold} (hr : ∀ i,0≤t i) {e z : ℝ} (_ : 0≤e) (hy : ∀ i : Listens C b (v:=m+1) hN p,
    t i*moneys C d k N p (v i.2)≤ z) (hs : Injective (seats C b Y hN p)) :
    let E:=readyStr m i Y b hN v h hp ht ℓ
    taxable (q:=Q.p) E t e (wilt Q.p.B*(3*z * debt Q.p.B (e+1) (halo 8 X.val))) := by
  intro F
  let f:= seats C b Y hN p
  let a x:=3*(t x*moneys C d k N p (v x.2)); have ha j : Taxed (F j) (q:=Q.p) t (a j):= hW_damp (v j.2) i h hp hN (hand C b hN p j) (fp C b hN p j) j (ht j.2) ℓ t (hr j)
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

lemma roil (hr : ∀ i,0 ≤ t i) {e z : ℝ} (hZ : ∀ i,c i≥0) (hx : ∀ i,t i*c i.2 ≤ z):
    Unpacks (readyNear m i Y b hN v h hp ht) Q.p t e (z * debt Q.p.B e X.val):= by
  let a x:=t x*c x.2;let F:=readyNear m i Y b hN v h hp ht
  have hh j: transported (F j) Q.p.threshold t (a j):= Rshot_cost (v j.2) i h hp hN (hand C b hN p j) (fp C b hN p j) j (ht j.2) t (hr j) (hZ _)
  have hp j:debt Q.p.B e (F j).extent=debt Q.p.B e X.val:=by unfold debt; rw [show _=swath _ _ X.val from (show (F j).extent=swath (hand C b hN p j) (seats C b Y hN p j) X.val from rfl),swath_cover]
  refine ⟨a,hh,shorten (A:=fun i=>(F i).fires) _ (fun i=>rfl) (fun j=>?_) fun i=>(hh i).1⟩
  rw [hp]; exact mul_le_mul_of_nonneg_right (hx _) (Real.exp_pos _).le

-- assembling long routes
lemma clouds (hr : ∀ i,0 ≤ t i) {e z : ℝ} (he : 0≤e) {q : BudgetPoint} (H : Lower (C.path.rep N p k).p q)
    (hc : scalesExp (C.path.rep N p k).p q (2*e)) (hy : ∀ i,t i*moneys C d k N p (v i.2) ≤ z):
    let A:= C.path.rep N p k
    let F:= readyWide m i Y b hN v h hp
    Credit F A.p q t e (Real.exp (100000*e)* Real.exp (-(A.p.supportExponent*i)/2) * z):= by
  intro D F
  let P:= D.p
  choose Fz hm Hm using fun j : Listens C b (v:=m+1) hN p => long_cost (ζ:=seats C b Y hN p) i (v j.2) h hp hN j (fp C b hN p j) (hand C b hN p j) e (C.path.rep N p k).p rfl H he hc t (hr j)
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
