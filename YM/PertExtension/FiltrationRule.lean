import YM.PertExtension.BareWords

/-!
# Top-Wilson diagram rule with offsets and basis columns

A kernel for the finite regulator calculation, including arbitrary *constant*
linear combinations of section columns prior to a formal finite-scheme solve.
At a common horizon; the engineering horizon used for the length factor of a
mark can vary. Does not assert that an arbitrary input matrix implements the
required top Wick compensation, nor existence of the limits after solving the
position conditions. -/
set_option autoImplicit false
set_option maxHeartbeats 900000
noncomputable section
namespace YM.PertExtension.LatticePT
open Wilson Lattice Gauge Precision Function Filter Set Metric MeasureTheory RG Labels Source
open scoped Topology ContDiff Classical BigOperators
open Chart Series Series.Tested Orb Orb.SlotEvaluation
variable {G : Gauge}{d : ℕ}{F : Labels.Frame G d}
variable {S : SectionData F}{h : Hol G}

def epsilon (q : ℕ+)(m : ℕ) := ((q:ℝ)^m)⁻¹
def nativePeriod (q : ℕ+)(m : ℕ) := 8*q.val^(m+1)*q.val^(m^2)
def side (q : ℕ+)(m : ℕ) : Side := ⟨nativePeriod q m,by unfold nativePeriod;positivity⟩
def period (q : ℕ+)(m : ℕ) := ((side q m).val:ℝ)*epsilon q m
@[simp] lemma period_eq q m : period q m=8*q*((q:ℝ)^(m^2)) := by
    change ((nativePeriod q m:ℕ):ℝ) * ((q:ℝ)^m)⁻¹=_
    unfold nativePeriod;push_cast; rw [pow_succ];field_simp
@[simp] lemma side_even q m : Even (side q m).val := ((by decide : Even 8).mul_right _).mul_right _
lemma epsilon_pos q m : 0<epsilon q m := inv_pos.mpr (by positivity)
lemma epsilon_zero {q : ℕ+}(hq : (1:ℕ)<q.val) : Tendsto (epsilon q) atTop (nhdsWithin 0 (Ioi 0)) := by
  have ht := (tendsto_pow_atTop_atTop_of_one_lt (r:=(q:ℝ)) (by exact_mod_cast hq)).inv_tendsto_atTop
  exact tendsto_inf.mpr ⟨ht, tendsto_principal.mpr (Eventually.of_forall fun m=>epsilon_pos ..)⟩

variable (q : ℕ+)(m : ℕ)
abbrev Native := Site (side q m)
def buffer := (side q m).val/8
def origins := (Finset.univ : Finset (Native q m)).filter fun p=>∀ a, buffer q m≤(p a).val ∧ (p a).val ≤2*buffer q m
lemma hasOrigin : (origins q m).Nonempty := by
  have h : buffer q m<(side q m).val := Nat.div_lt_self (side q m).pos (by norm_num)
  refine ⟨(fun _=>(buffer q m:ZMod (side q m).val)),Finset.mem_filter.mpr ⟨by simp,fun a=>?_⟩⟩
  rw [ZMod.val_natCast_of_lt h]; omega
lemma origin_pos : 0< (origins q m).card:= Finset.card_pos.mpr (hasOrigin q m)

def point (x : Native q m): E4 := epsilon q m • WithLp.toLp 2 fun i => (Lattice.lift x i:ℝ)

section Stencils
variable {I : Type*} [Fintype I] (B : I → F.Index→ℝ)(w : I→ℕ)
variable (Ψ : (I→E4)→ℝ)(S)
variable (x : I→ Native q m)(o : Native q m)(t : I → F.Index)
def placed (j : I) := x j+o
def column (i : I) := (epsilon q m)^4/(epsilon q m)^(w i) * B i (t i)
def packet := joints Finset.univ t (placed q m x o) (column q m B w t) (C:=S)
def nSlots := ∑ i, (F.grades (t i)).2
private def weight := ((origins q m).card:ℝ)⁻¹ * Ψ (fun i=> point q m (x i))
def termNode (g:ℝ) := (g⁻¹)^(nSlots t) * preExpectation (packet S q m B w x o t) g
def diagNode (j : ℕ) := diagonalWith (tray G) (restrictedO (packet S q m B w x o t)) (nSlots t+j)

def physicalRead : ℝ→ℝ := ∑ z:I→Native q m,∑ u∈origins q m,weight q m Ψ z • (∑ v:I→F.Index,termNode S q m B w z u v)
def diagramRead : ℕ→ℝ := ∑ z:I→Native q m,∑ u∈origins q m,weight q m Ψ z • (∑ v:I→F.Index,diagNode S q m B w z u v)

def insertion (g : ℝ) := ∑ z:I→Native q m,∑ u∈origins q m,∑ v:I→F.Index,(weight q m Ψ z * (g⁻¹)^(nSlots v)) • packet S q m B w z u v

private lemma preNumSum {n : Side}{V:Type*}(A : V→Config G n→ℝ)(c : V→ℝ)(s : Finset V) (hc:∀ i∈s, Continuous (A i)) (t : ℝ) :
    preNum (∑ i∈s,c i • A i) t = ∑ i∈s,c i * preNum (A i) t := by
   let z:= fun v:OEdge n→G.El => preDensity t (liftLinks v)
   have he : Continuous z := by
     refine Real.continuous_exp.comp ((((energy_cont.comp ?_).div_const 2).neg).div_const (t^2))
     apply continuous_pi; intro i; unfold liftLinks;split <;> fun_prop
   have hi {i:V}(hx : i∈s) : Integrable (fun v=> (c i * A i (liftLinks v))*z v) (physical G (OEdge n)) := by
      apply Continuous.integrable_of_hasCompactSupport _ (HasCompactSupport.of_compactSpace _)
      exact (continuous_const.mul ((hc i hx).comp (lift_cont G))).mul he
   unfold preNum; simp_rw [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,Finset.sum_mul]
   rw [MeasureTheory.integral_finsetSum _ (@fun i hi' =>?_)]; swap
   · exact hi hi'
   apply Finset.sum_congr rfl fun i hi=>?_ ; simp_rw [mul_assoc,MeasureTheory.integral_const_mul]

lemma read_single_denominator (g : ℝ) : physicalRead S q m B w Ψ g=preNum (insertion S q m B w Ψ g) g / preNum (1:Config G (side q m)→ℝ) g := by
  let n:=side q m
  let T:=Native q m
  have hp z u v : Continuous (packet S q m B w z u v) := by unfold packet Orb.SlotEvaluation.joints -- name adjust
                                                            apply continuous_finsetProd _ fun i _=>?_
                                                            exact continuous_const.mul ((Complex.continuous_re).comp (SectionData.continuous_places S _ _))
  let c := weight q m Ψ
  let A := packet S q m B w
  let ι:=Finset.univ (α:=I→F.Index)
  let X:=Finset.univ (α:=I→T)
  let Y:=origins q m
  have h₁ z u: preNum (∑ i∈ι,(c z*(g⁻¹)^nSlots i) • A z u i) g=∑ i∈ι,c z*(g⁻¹)^nSlots i * preNum (A z u i) g := by
    apply preNumSum; exact fun i _=>hp z u i
  let O (z:I→T) (u:T) := ∑ i∈ι, ((c z*(g⁻¹)^nSlots i) • A z u i)
  have ho z u : Continuous (O z u):=by
    change Continuous (fun x=>O z u x)
    simp only [O,Finset.sum_apply,Pi.smul_apply];exact continuous_finsetSum _ fun i hi=> by convert! Continuous.const_smul (hp z u i) (c z * (g⁻¹)^nSlots i) <;> rfl
  let f z:=∑ u∈Y,O z u
  have hf z:Continuous (f z):=by
    change Continuous (fun x=>f z x)
    simp only [f,Finset.sum_apply];exact continuous_finsetSum _ fun u _=>ho z u
  have he : preNum (insertion S q m B w Ψ g) g=∑ z∈X,∑ u∈Y,∑ i∈ι,(c z*(g⁻¹)^nSlots i)*preNum (A z u i) g := by
    apply Eq.trans (b:=∑ z∈X,preNum (f z) g)
    · convert preNumSum f (fun _=>1) X (fun z _=>hf z) g using 2 <;> simp [insertion,c,A,O,f,X,Y,ι,T,n]
    apply Finset.sum_congr rfl fun z hz=>?_;unfold f
    have ht : preNum (∑ u∈Y,O z u) g = ∑ u∈Y,preNum (O z u) g := by simpa only [one_mul,one_smul] using! preNumSum  (O z) (fun _=>1) Y (fun u _=>ho z u) g
    exact ht.trans (Finset.sum_congr rfl fun u hu=>h₁ z u)
  rw [he]
  unfold physicalRead termNode
  simp_rw [Finset.sum_div];simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul, Finset.mul_sum, preExpectation]
  simp_rw [←mul_assoc,←mul_div_assoc];rfl

private lemma priced (φ : ℝ→ℝ)(a : ℕ→ℝ)(c : ℝ)(h : Aspiration φ a) :Aspiration (c • φ) (c • a) := by
  intro j;obtain ⟨A,hA,H⟩:=h j
  refine ⟨‖c‖*A,mul_nonneg (norm_nonneg _) hA,?_⟩
  filter_upwards [H] with t ht
  have hp : (c • φ - peval (c • a) j) t=c*((φ-peval a j) t):=by dsimp [peval,Zone.eval,Pi.sub_apply];rw [mul_sub,Finset.mul_sum];congr 1;apply Finset.sum_congr rfl;intro;intro;ring
  rw [hp,norm_mul]; exact (mul_le_mul_of_nonneg_left ht (norm_nonneg _)).trans_eq (mul_assoc _ _ _).symm

lemma packet_comparison (hh : S.Sound h)(hv : Bid.pop S):
    Aspiration (termNode S q m B w x o t) (diagNode S q m B w x o t) := by
  unfold termNode diagNode
  exact joint_finite (h:=hh) (p:=hv) _ _ _ _ (traySpec G) (side_even ..)

theorem finite (hh : S.Sound h)(hv : Bid.pop S): Aspiration (physicalRead S q m B w Ψ) (diagramRead S q m B w Ψ):=
  Aspiration.sum _ _ _ fun x hx=> Aspiration.sum _ _ _ fun o ho=>priced _ _ _ <| Aspiration.sum _ _ _ fun t ht=>packet_comparison S q m B w x o t hh hv

private lemma basis_bound (j i : ℕ)(ho : Odd (j+nSlots t)) (hi : i=j) : diagNode S q m B w x o t i=0:= by
  subst i; unfold diagNode
  exact normalized_odd (R:=traySpec G) (even:=side_even ..) (O:=restrictedO _) (hk:=by simpa [add_comm] using ho)

theorem oddRead (j : ℕ) (H : ∀ t : I→F.Index, (∀ i,B i (t i)≠0) → Odd (j+nSlots t)) : diagramRead S q m B w Ψ j=0:= by
  simp only [diagramRead,Finset.sum_apply, Pi.smul_apply,smul_eq_mul]
  refine Finset.sum_eq_zero fun x _=> Finset.sum_eq_zero fun o _=> mul_eq_zero_of_right _ (Finset.sum_eq_zero fun t _=>?_)
  by_cases hm : ∃ i,B i (t i)=0
  · obtain ⟨i,hi⟩:=hm; have hf : packet S q m B w x o t=0:=by
      funext v
      unfold packet joints
      exact Finset.prod_eq_zero (Finset.mem_univ i) (by unfold column;rw [hi]; simp)
    simp only [diagNode,hf]; change diagonalWith _ 0 _ = _
    have hco : diagonalWith (tray G) (n:=side q m) 0 = 0:=by
      have ht : expectation (0:Observable G (side q m))=0:=by funext a; unfold expectation numerator entries; simp
      have htest := (finite_formula (P:=tray G) (side_even q m) (traySpec G) (O:=0) ⟨continuous_const,contDiffAt_const⟩)
      have hz := Aspiration.single (0:ℝ) 0
      rw [show (fun r:ℝ=>r^(0:ℕ) • (0:ℝ))=0 from funext (by simp), show (fun i : ℕ=>if i=0 then (0:ℝ) else 0)=0 from by ext i;simp] at hz
      rw [ht] at htest
      exact htest.unique hz
    rw [hco];rfl
  exact (basis_bound S q m B w x o t j j) (H t (by simpa using hm)) rfl

end Stencils
end YM.PertExtension.LatticePT
