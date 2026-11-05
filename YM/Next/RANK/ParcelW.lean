import YM.Next.RANK.Post
import YM.Next.RANK.Strat

/-!
# Frame assembled at the restart

Connect the probe tilt and residual of uncorrected laws with all markers,
including full old masks even when G.S divides by beta.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Edition
open Function Filter RG Thirst Lattice Wilson MeasureTheory Relation Corona Value Glyph Marker Perch Vac.Numbers Alarm Spindle Station Cells Atlas Finset Baler Source Labels EntryWord Exponential
open scoped BigOperators Classical Topology Matrix.Norms.Frobenius

variable {G : Gauge} {n : Side} {C : Family G} {ι κ χ μ V : Type} [Fintype V] [DecidableEq V]
variable [Fintype ι] [Fintype κ]
variable {N k d p m : ℕ} {q : BudgetPoint} {ζ : V→Site n} {τ : ℝ}

-- combine alarm expo real character
lemma real_mul (x : ℝ) (U : veil V) : Nreal x*U=(x:ℂ) • U := by change ((x:ℂ) • (1 : veil V))*U=_; rw [smul_mul_assoc,one_mul]

lemma grow_head {P S : Rep G n} {X : Siren G n τ} {W : κ→ Wickless G n τ} (L : ι→Strike G ζ τ) (U : Config G n)
    (hp : Real.exp (P.exponent U)=Real.exp (S.exponent U)*(∏ j,((W j).value U+1))*∏ j∈flags τ U,X.value j U) :
    Nreal (Real.exp (P.exponent U)) * (∏ j,((L j).occ U+1))= Nreal (V:=V) (Real.exp (S.exponent U))* (
       (∏ j∈flags τ U,Nreal (X.value j U))*∏ i:κ⊕ι,((Sum.elim (fun j=> (W j).credit ζ) L i).occ U+1)) := by
  rw [hp,map_mul,map_mul,map_prod,map_prod,Fintype.prod_sum_type]; simp_rw [map_add,map_one, Sum.elim_inl,Sum.elim_inr,vacant]; ring

lemma orbitNil (M Q F : veil V) (h : M=Q+F) (H : Q.part (quiet _)=0) (hF : F.part (quiet _)=0) : Poly.pass M=Poly.pass Q* Poly.pass F:= by rw [h]; exact pass_add Q F H hF
lemma charge_por [Fintype μ] [Fintype χ]
    {P Q : Rep G n} {X : Siren G n Q.p.threshold} {W : κ→ Wickless G n Q.p.threshold} (L : ι→Strike G ζ Q.p.threshold)
    (A : μ→ Lifted G ζ P.p.threshold) (H : χ→ SourceAt G ζ) (U : Config G n) {u : veil V} (H₁ : Q.p.threshold ≤ P.p.threshold)
    (hp : Real.exp (P.exponent U)=Real.exp (Q.exponent U)*(∏ j,((W j).value U+1))*∏ j∈flags Q.p.threshold U,X.value j U)
    (he : ∀ i,(L i).fires.val.Nonempty) (hv : u= (∑ i,(H i).amount Q.p.threshold U)+∑ i,(L i).occ U) :
    (Real.exp (P.exponent U):ℂ) • (Poly.pass u*∑ j:Finset μ,Lifted.pack A j U)=
      dust Q H (teat A (Sum.elim (fun j=> (W j).credit ζ) L) X) U := by
  rw [dust, ← real_mul, ← real_mul, ← charade A _ X U H₁]; let F :=∑ i,(H i).amount Q.p.threshold U
  let V:= Poly.pass F; have h (i):((L i).occ U).part (quiet _)=0 := send_zero _ _ (he i)
  have hh := orbitNil u F _ hv (by unfold F; rw [Poly.part_sum]; exact sum_eq_zero fun i _=> send_zero _ _ (H i).chosen)
    (by rw [Poly.part_sum]; exact sum_eq_zero fun i _=> h i)
  have hz : Poly.pass u=V*∏ i,((L i).occ U + 1):= by rw [hh,pass_sum _ _ (fun i _=> h i)]; dsimp only [V]; congr 1; exact Finset.prod_congr rfl fun i _=> solo_pass _ _ (he i)
  rw [hz]
  let C : veil _:=∑ j:Finset μ,Lifted.pack A j U; let p:=Real.exp (P.exponent U)
  let M: veil _:=∏ i, ((L i).occ U+1)
  rw [show Nreal p* (V*M*C)=(Nreal p*M)*V*C by ring, grow_head (X:=X) L U hp]; dsimp only [C,V,F]; ring

variable (m i : ℕ) (Y : Points (m+1)) (s : ℝ) (hN : k≤N) (v : Fin (m+1)→C.label d)
variable {Q : Rep G (C.side k p)} {B : Neat (C.side k p)→Burst G (C.side k p) (C.path.rep N p k).p.threshold}
variable {X : Keepat (C.side k p)} {w : Fin (m+1) → Config G (C.side k p)→ℂ} {c : Fin (m+1)→ℝ}

section
variable (A : ι → SourceAt G (seats C s Y hN p)) (L : κ → Lifted G (seats C s Y hN p) (C.path.rep N p k).p.threshold)
variable (h : C.Makes) (hp : C.ref d≤k) (ht : ∀ j,Ticket (v j) i k N p Q.p X (w j) (c j))

def readyH (j : Listens C s (v:=m+1) hN p) := openW (v j.2) i (hand C s hN p j) (fp C s hN p j) j (ht j.2) (ζ:=seats C s Y hN p)
def readyNear (j : Listens C s (v:=m+1) hN p) := Rshot (v j.2) i h hp hN (hand C s hN p j) (fp C s hN p j) j (ht j.2) (ζ:=seats C s Y hN p)
def readyWide (j : Listens C s (v:=m+1) hN p × Keepat (C.side k p)) :=
    docket i (v j.1.2) h hp hN j.1 (fp C s hN p j.1) (hand C s hN p j.1) j.2 (ζ:=seats C s Y hN p)
def readyStr (H : Q.p.threshold≤(C.path.rep N p k).p.threshold) (j : Listens C s (v:=m+1) hN p) :=
    Ember (v j.2) i h hp hN (hand C s hN p j) (fp C s hN p j) j (ht j.2) H (ζ:=seats C s Y hN p)

def stand (ℓ : Q.p.threshold ≤ (C.path.rep N p k).p.threshold) := Sum.elim (readyStr m i Y s hN v h hp ht ℓ)
    (fun i' => dash (C.path.rep N p k).p Q.p (Sum.elim A (readyWide m i Y s hN v h hp) i') ℓ)
def rested := Sum.elim (readyNear m i Y s hN v h hp ht) (Sum.elim A (readyWide m i Y s hN v h hp))

lemma power (ℓ : Q.p.threshold ≤ (C.path.rep N p k).p.threshold) (U : Config G (C.side k p)) :
    let P:= C.path.rep N p k; let S:= C.localSection d;let a:=P.p.threshold;let b:= Q.p.threshold
    let f:=pinHat C d k
    let H:=Sum.elim (rested m i Y s hN v A h hp ht) (readyH m i Y s hN v ht);let L:= stand m i Y s hN v A h hp ht ℓ
    (∑ j,Poly.send (slot j) (dot (fp C s hN p j) (f* (press hN s v j).exponentialEntry 0 S P (puller C s Y hN p j U)))) + (∑ i,(A i).amount a U) = (∑ i,(H i).amount b U)+(∑ i, (L i).occ U):= by
  intro P S a b f H L
  let Z:=Sum.elim A (readyWide m i Y s hN v h hp); let F (j:Listens C s (v:=m+1) hN p):=Poly.send (slot j) (dot (fp C s hN p j) (f* (press hN s v j).exponentialEntry 0 S P (puller C s Y hN p j U)))
  let X:=readyStr m i Y s hN v h hp ht ℓ; let O:=readyH m i Y s hN v ht; let B:=readyNear m i Y s hN v h hp ht
  have he i u : (Z i).amount a u=(Z i).amount b u+(dash P.p Q.p (Z i) ℓ).occ u:= dash_amount ..
  rw [Fintype.sum_sum_type (f:= fun j=> (H j).amount b U),show (∑ i,(H (Sum.inl i)).amount b U)=_ from Fintype.sum_sum_type _, Fintype.sum_sum_type (f:= fun j=>(L j).occ U)]
  change _ = (((∑ i,(B i).amount b U)+(∑ i,(Z i).amount b U))+(∑ i,(O i).amount b U))+
      ((∑ i,(X i).occ U)+(∑ i,(dash P.p Q.p (Z i) ℓ).occ U))
  have hx : ∑ i,(Z i).amount b U + ∑ i,(dash P.p Q.p (Z i) ℓ).occ U= ∑ i,(Z i).amount a U:= by rw [←sum_add_distrib]; exact sum_congr rfl fun i _=> (he i U).symm
  let W := readyWide (p:=p) m i Y s hN v h hp
  have hq : ∑ i,F i=∑ i,(O i).amount b U + (∑ i,(B i).amount b U)+ (∑ i,(X i).occ U)+(∑ i,(W i).amount a U):= by
    rw [Fintype.sum_prod_type (fun i=> (W i).amount a U), ← sum_add_distrib,← sum_add_distrib,← sum_add_distrib]; apply sum_congr rfl; intro x _
    unfold F; let V:= puller C s Y hN p x U;let P':=v x.2
    let g:=fp C s hN p x
    change Poly.send _ (dot g (awakeFull C k N p (v x.2) V))=_
    rw [cost_ex _ h hp hN i V,dot_add,send_plus]; exact congr_arg₂ (·+·) (snow ..) (portion ..).symm
  have hz : ∑ i,(A i).amount a U+(∑ i,(W i).amount a U)= ∑ i,(Z i).amount a U:= (Fintype.sum_sum_type (fun i=> (Z i).amount a U)).symm
  change (∑ i,F i)+_= _; rw [hq];
  linear_combination (norm:=abel) hz-hx


omit [Fintype ι] in
lemma standMode (ℓ : Q.p.threshold ≤ (C.path.rep N p k).p.threshold) j : ((stand m i Y s hN v A h hp ht ℓ) j).fires.val.Nonempty := by
  rcases j with y|j
  · exact singleton_nonempty _
  exact (Sum.elim A (readyWide (p:=p) m i Y s hN v h hp) j).chosen
set_option synthInstance.maxSize 512 in

lemma assembled (F : Siren G (C.side k p) Q.p.threshold) (W : ValidX (C.side k p)→ Wickless G _ Q.p.threshold) {a b σ T Λ δ : ℝ} (ℓ : Q.p.threshold ≤ (C.path.rep N p k).p.threshold)
    (hp' : Bridges (C.path.rep N p k) Q a b σ T Λ δ F W (q:=Q.p)) U :
    fabricated Y hN s v B A L h hp U=dust Q (Sum.elim (rested m i Y s hN v A h hp ht) (readyH m i Y s hN v ht))
      (teat (Sum.elim (ensembleO Y hN s v B h hp) L) (Sum.elim (fun i=> (W i).credit (seats C s Y hN p)) (stand m i Y s hN v A h hp ht ℓ)) F) U := by
  exact charge_por (H₁:=ℓ) _ _ _ _ (hp'.predicts U) (standMode m i Y s hN v A h hp ht ℓ) (power m i Y s hN v A h hp ht ℓ U)
end
end YM.Next.Rank.Edition
