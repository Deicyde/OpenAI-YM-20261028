import YM.MergeProof.West.Dart
import YM.Next.RANK.ParcelW
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Edition
open Function Filter RG Thirst Lattice Wilson MeasureTheory Relation Corona Value Glyph Marker Perch Vac.Numbers Alarm Spindle Station Cells Atlas Finset Baler Source Labels EntryWord Exponential
open scoped BigOperators Classical Topology Matrix.Norms.Frobenius

variable {G : Gauge} {n : Side} {C : Family G} {ι κ χ μ V : Type} [Fintype V] [DecidableEq V]
variable [Fintype ι] [Fintype κ]
variable {N k d p m : ℕ} {q : BudgetPoint} {ζ : V→Site n} {τ : ℝ}

variable (m i : ℕ){d:Fin (m+1) → ℕ} (Y : Points (m+1)) (s : ℝ) (hN : k≤N) (v : (i:Fin (m+1))→ C.label (d i))
variable {Q : Rep G (C.side k p)} {B : Neat (C.side k p)→Burst G (C.side k p) (C.path.rep N p k).p.threshold}
variable {X : Keepat (C.side k p)} {w : Fin (m+1) → Config G (C.side k p)→ℂ} {c : Fin (m+1)→ℝ}

section
variable (A : ι → SourceAt G (seats C s Y hN p)) (L : κ → Lifted G (seats C s Y hN p) (C.path.rep N p k).p.threshold)
variable (h : C.Makes) (hp : ∀ i,C.ref (d i) ≤ k) (ht : ∀ j,Ticket (v j) i k N p Q.p X (w j) (c j))

def readyHX (j : Listens C s (v:=m+1) hN p) := openW (v j.2) i (hand C s hN p j) (fp C s hN p j) j (ht j.2) (ζ:=seats C s Y hN p)
def readyNearX (j : Listens C s (v:=m+1) hN p) := Rshot (v j.2) i h (hp j.2) hN (hand C s hN p j) (fp C s hN p j) j (ht j.2) (ζ:=seats C s Y hN p)
def readyWideX (j : Listens C s (v:=m+1) hN p × Keepat (C.side k p)) :=
    docket i (v j.1.2) h (hp j.1.2) hN j.1 (fp C s hN p j.1) (hand C s hN p j.1) j.2 (ζ:=seats C s Y hN p)
def readyStrX (H : Q.p.threshold≤(C.path.rep N p k).p.threshold) (j : Listens C s (v:=m+1) hN p) :=
    Ember (v j.2) i h (hp j.2) hN (hand C s hN p j) (fp C s hN p j) j (ht j.2) H (ζ:=seats C s Y hN p)

def standX (ℓ : Q.p.threshold ≤ (C.path.rep N p k).p.threshold) := Sum.elim (readyStrX m i Y s hN v h hp ht ℓ)
    (fun i' => dash (C.path.rep N p k).p Q.p (Sum.elim A (readyWideX m i Y s hN v h hp) i') ℓ)
def restedX := Sum.elim (readyNearX m i Y s hN v h hp ht) (Sum.elim A (readyWideX m i Y s hN v h hp))

lemma powerX (ℓ : Q.p.threshold ≤ (C.path.rep N p k).p.threshold) (U : Config G (C.side k p)) :
    let P:= C.path.rep N p k; let S:= fun x:Fin (m+1)=> C.localSection (d x);let a:=P.p.threshold;let b:= Q.p.threshold
    let f:=fun x => pinHat C (d x) k
    let H:=Sum.elim (restedX m i Y s hN v A h hp ht) (readyHX m i Y s hN v ht);let L:= standX m i Y s hN v A h hp ht ℓ
    (∑ j,Poly.send (slot j) (dot (fp C s hN p j) (f j.2 * (pressX hN s v j).exponentialEntry 0 (S j.2) P (puller C s Y hN p j U)))) + (∑ i,(A i).amount a U) = (∑ i,(H i).amount b U)+(∑ i, (L i).occ U):= by
  intro P S a b f H L
  let Z:=Sum.elim A (readyWideX m i Y s hN v h hp); let F (j:Listens C s (v:=m+1) hN p):=Poly.send (slot j) (dot (fp C s hN p j) (f j.2 * (pressX hN s v j).exponentialEntry 0 (S j.2) P (puller C s Y hN p j U)))
  let X:=readyStrX m i Y s hN v h hp ht ℓ; let O:=readyHX m i Y s hN v ht; let B:=readyNearX m i Y s hN v h hp ht
  have he i u : (Z i).amount a u=(Z i).amount b u+(dash P.p Q.p (Z i) ℓ).occ u:= dash_amount ..
  rw [Fintype.sum_sum_type (f:= fun j=> (H j).amount b U),show (∑ i,(H (Sum.inl i)).amount b U)=_ from Fintype.sum_sum_type _, Fintype.sum_sum_type (f:= fun j=>(L j).occ U)]
  change _ = (((∑ i,(B i).amount b U)+(∑ i,(Z i).amount b U))+(∑ i,(O i).amount b U))+
      ((∑ i,(X i).occ U)+(∑ i,(dash P.p Q.p (Z i) ℓ).occ U))
  have hx : ∑ i,(Z i).amount b U + ∑ i,(dash P.p Q.p (Z i) ℓ).occ U= ∑ i,(Z i).amount a U:= by rw [←sum_add_distrib]; exact sum_congr rfl fun i _=> (he i U).symm
  let W := readyWideX (p:=p) m i Y s hN v h hp
  have hq : ∑ i,F i=∑ i,(O i).amount b U + (∑ i,(B i).amount b U)+ (∑ i,(X i).occ U)+(∑ i,(W i).amount a U):= by
    rw [Fintype.sum_prod_type (fun i=> (W i).amount a U), ← sum_add_distrib,← sum_add_distrib,← sum_add_distrib]; apply sum_congr rfl; intro x _
    unfold F; let V:= puller C s Y hN p x U;let P':=v x.2
    let g:=fp C s hN p x
    change Poly.send _ (dot g (awakeFull C k N p (v x.2) V))=_
    rw [cost_ex _ h (hp x.2) hN i V,dot_add,send_plus]; exact congr_arg₂ (·+·) (snow ..) (portion i (v x.2) h (hp x.2) hN x g (hand C s hN p x) U).symm
  have hz : ∑ i,(A i).amount a U+(∑ i,(W i).amount a U)= ∑ i,(Z i).amount a U:= (Fintype.sum_sum_type (fun i=> (Z i).amount a U)).symm
  change (∑ i,F i)+_= _; rw [hq];
  linear_combination (norm:=abel) hz-hx


omit [Fintype ι] in
lemma standModeX (ℓ : Q.p.threshold ≤ (C.path.rep N p k).p.threshold) j : ((standX m i Y s hN v A h hp ht ℓ) j).fires.val.Nonempty := by
  rcases j with y|j
  · exact singleton_nonempty _
  exact (Sum.elim A (readyWideX (p:=p) m i Y s hN v h hp) j).chosen
set_option synthInstance.maxSize 512 in

lemma assembledX (F : Siren G (C.side k p) Q.p.threshold) (W : ValidX (C.side k p)→ Wickless G _ Q.p.threshold) {a b σ T Λ δ : ℝ} (ℓ : Q.p.threshold ≤ (C.path.rep N p k).p.threshold)
    (hp' : Bridges (C.path.rep N p k) Q a b σ T Λ δ F W (q:=Q.p)) U :
    fabricatedX Y hN s v B A L h hp U=dust Q (Sum.elim (restedX m i Y s hN v A h hp ht) (readyHX m i Y s hN v ht))
      (teat (Sum.elim (ensembleOX Y hN s v B h hp) L) (Sum.elim (fun i=> (W i).credit (seats C s Y hN p)) (standX m i Y s hN v A h hp ht ℓ)) F) U := by
  exact charge_por (H₁:=ℓ) _ _ _ _ (hp'.predicts U) (standModeX m i Y s hN v A h hp ht ℓ) (powerX m i Y s hN v A h hp ht ℓ U)
end
end YM.Next.Rank.Edition
