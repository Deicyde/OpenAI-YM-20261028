import YM.Next.RANK.Radian.Indices

/-!
# Recycle heat smoothing at far momentum (rapid derivative decay)

Avoid algebraic matrix inversion estimates (prerequisite). This is to concatenate k-unit
factor jets with lengths and wrap-phase derivatives, once seal stamped. -/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Radian
open MeasureTheory Measure Filter Maxwell Topology Analysis Asymptotics Set Real Metric Beamer Lattice Prayer Finset
open scoped ContDiff Topology BigOperators Classical NNReal ENNReal FourierTransform RealInnerProductSpace
local notation "ℑ" => Complex.I

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {G : Gauge} {i j d : ℕ} {x y t : ℝ}

lemma optics (Q : ContinuousMultilinearMap ℝ (fun _:Fin d=>E4) E) (he : 0 ≤ t) (H : ∀ i:Fin d → Axis, ‖Q (YM.basis ∘ i)‖ ≤ t): ‖Q‖ ≤ (Fintype.card (Fin d→Axis):ℝ)*t := by
  refine ContinuousMultilinearMap.opNorm_le_bound (by positivity) fun m=>?_ ; let F (i : Fin d) (j : Axis):=(m i j) • basis j
  have he : Q m=∑ t:Fin d→Axis,Q fun i=> F i (t i) := by
    have hp : (fun i=>∑ j,F i j) = m:= by ext i a; simp [F]
    exact (congr_arg Q hp.symm).trans (Q.toMultilinearMap.map_sum F)
  rw [he]; apply (norm_sum_le ..).trans
  let p:=∏ i,‖m i‖; refine le_trans (Finset.sum_le_sum (g:=fun _=>t*p) ?_) ?_; swap
  · rw [sum_const, nsmul_eq_mul,card_univ,mul_assoc]
  intro i _
  have h (s : Fin d): ‖m s (i s)‖≤‖m s‖:= by rw [Real.norm_eq_abs,← YM.basis_inner]; exact (abs_real_inner_le_norm ..).trans_eq (by rw [YM.basis_norm,one_mul])
  rw [show Q (fun j=>F j (i j))=(∏ j, m j (i j)) • Q (YM.basis∘ i) from ?_,norm_smul,Real.norm_eq_abs,Finset.abs_prod]; swap; exact Q.map_smul_univ _ _
  rw [mul_comm]; exact mul_le_mul (H _) (Finset.prod_le_prod (fun i _=>abs_nonneg _) (fun i _=>h i)) (Finset.prod_nonneg (fun _ _=>abs_nonneg _)) (by assumption)

def Fast (f : E4→ℂ):= (∀ x∈away,ContDiffAt ℝ ∞ f x) ∧ ∀ i n:ℕ,∃ C : ℝ, 0≤C ∧ ∀ x:E4,1 ≤ ‖x‖ →‖x‖^n *‖iteratedFDeriv ℝ i f x‖ ≤ C
lemma susp {f : E4→ℂ} (H : ∀ x∈away,ContDiffAt ℝ ∞ f x) (v : ∀ (l : List Axis) (i : ℕ),∃ C,0≤C∧∀ x:E4,1≤‖x‖ → ‖x‖^i * ‖dV l f x‖≤C) : Fast f:= by
  refine ⟨H,fun i n=>?_⟩; let t := Fin i → Axis; choose C hp Hq using fun l:t=> v (List.ofFn l).reverse n
  let p:=∑ l,C l;have hb:0≤p:=sum_nonneg fun i _=>hp _
  refine ⟨(Fintype.card t:ℝ)*p,mul_nonneg (by positivity) hb,fun x hx=>?_⟩
  have hz:0 < ‖x‖^n:= pow_pos (zero_lt_one.trans_le hx) _
  let T:=iteratedFDeriv ℝ i f x
  have he (l:t): ‖T (basis ∘ l)‖ ≤ p/‖x‖^n:= by
    apply (le_div_iff₀ hz).2; let hT:= Hq l x hx; rw [dVcoeff i l H (show x∈away from norm_pos_iff.mp (zero_lt_one.trans_le hx))] at hT
    simp only [Tensor.coeff,_root_.smul_apply, smul_smul,mul_inv_cancel₀ (show (i.factorial:ℝ)≠0 by positivity),one_smul] at hT
    rw [mul_comm]; exact hT.trans (single_le_sum (f:=C) (fun _ _=> hp _) (mem_univ _))
  apply (mul_le_mul_of_nonneg_left (optics T (div_nonneg hb hz.le) he) hz.le).trans_eq; field_simp;exact mul_comm ..
lemma rapidG {F : E4→ℝ} (H : Spire F) {b : ℝ} (h : 0<b) : Fast (fun x:E4=>(↑((F*blaze b) x):ℂ)):= by
  have he x (hx:x∈away):ContDiffAt ℝ ∞ (F*blaze b) x:= (H.smooth hx).mul (Real.contDiff_exp.contDiffAt.comp _ (contDiffAt_const.mul (contDiff_norm_sq ℝ).contDiffAt))
  refine susp (fun x hx=> Complex.ofRealCLM.contDiff.contDiffAt.comp _ (he x hx)) fun l i=>?_
  obtain ⟨c,hc,hq⟩:=faded H h l i; refine ⟨c,hc,fun x hx=>?_⟩;have he:= echoes l he (show x∈away from norm_pos_iff.mp (zero_lt_one.trans_le hx)); rw [he]; rw [Complex.norm_real]; exact hq x hx
lemma Fast.sub {f g : E4→ℂ} (h : Fast f) (o : Fast g): Fast (f-g):= by
  refine ⟨fun x hx=> (h.1 x hx).sub (o.1 x hx),fun i n=>?_⟩
  obtain ⟨A,hA,H⟩:=h.2 i n; obtain ⟨b,hB,hv⟩:=o.2 i n; refine ⟨A+b,add_nonneg hA hB,fun x hx=>?_⟩; have he:x∈away:= norm_pos_iff.mp (zero_lt_one.trans_le hx)
  rw [iteratedFDeriv_sub_apply ((h.1 x he).of_le (WithTop.coe_le_coe.mpr le_top)) ((o.1 x he).of_le (WithTop.coe_le_coe.mpr le_top))];apply (mul_le_mul_of_nonneg_left (norm_sub_le ..) (pow_nonneg (norm_nonneg _) _)).trans; rw [mul_add];exact add_le_add (H x hx) (hv x hx)
lemma Fast.scale {f : E4→ℂ} (h : Fast f) (v : ℂ) : Fast (v • f):= by
  refine ⟨fun x hx=> (h.1 x hx).const_smul v,fun i n=>?_⟩
  obtain ⟨C,hC,hT⟩:= h.2 i n; refine ⟨‖v‖*C, by positivity,fun x hx=>?_⟩
  rw [iteratedFDeriv_const_smul_apply (𝕜:=ℝ) ((h.1 _ (show x∈away from norm_pos_iff.mp (zero_lt_one.trans_le hx))).of_le (WithTop.coe_le_coe.mpr le_top)),norm_smul,mul_left_comm]; exact mul_le_mul_of_nonneg_left (hT x hx) (norm_nonneg _)
lemma Fast.zero : Fast 0:= ⟨fun i hi=>contDiffAt_const,fun i n=> ⟨0,le_rfl,fun x hx=>by simp⟩⟩

lemma orbit (b : ℝ) (l : List Axis): ∃ c:ℂ,∃ f:E4→ℝ, Spire f∧ press l (liturgy b) = c • fun x=>(↑((f*blaze b) x):ℂ):= by
  induction l with
  | nil=>
    refine ⟨(↑Maxwell.normal:ℂ),spike,.hill,funext fun i=>?_⟩; unfold liturgy press; dsimp only [List.foldr_nil]; dsimp only [spike,blaze,major,Pi.smul_apply,Pi.mul_apply,smul_eq_mul]; push_cast; ring
  | cons i s IH=>
    obtain ⟨c,f,h,H⟩:=IH; refine ⟨(2*(π:ℂ)*ℑ)*c,(pin i)*f,(Spire.ascend i).product h,?_⟩
    change crank i (press s _) = _; rw [H]; ext1 v; simp only [Pi.smul_apply, crank,chirp,pin,Pi.mul_apply, Complex.ofReal_mul,smul_eq_mul];ring

lemma looks {b : ℝ} (h : 0<b) (t q : Degree G) : Fast (HeatP b t q):= by
  have he (v : List Axis): Fast (press v (liturgy b)):= by obtain ⟨c,f,H,hv⟩:= orbit b v; rw [hv]; exact (rapidG H h).scale _
  unfold HeatP paints; split;swap; exact Fast.zero
  apply Fast.scale; apply Fast.sub (Fast.sub ?_ ?_) (Fast.sub ?_ ?_) <;> split <;> first|apply he|exact Fast.zero
end YM.Next.Rank.Radian
