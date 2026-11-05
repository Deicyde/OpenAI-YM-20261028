import YM.Planned.PRIMARY_INTEGRAL_295.Little

/-!
# Fixed-L Gap at flat V for genuine PreGram cut includes every torus harmonic

Only one positive channel suffices here. `E.F1` proof for D *not*
using nonlinear test Hessian/red alignment inputs. Physical group price and
fderiv on real chart. Post λ(L) no claim pre-L. This is on exact cut rows,
without smoothness at guard plateaux. -/
set_option autoImplicit false
noncomputable section
namespace YM.Planned.PrimaryIntegral295.Bosom
open Function Filter Set Metric
open Labels Lattice RG Wilson Pressure Precision Exterior Tree Streets Carrier Bloch Place
open Villa Fizz Fizz.Gush Bazaars
open Bid (pulled bills Sworn stretch)
open Next.Free Next.Fluctuations Bunks Little Work.F01 Little.Core
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius RealInnerProductSpace Classical
variable {G : Gauge} {z n k:ℕ} {c f : Side} {S : StepData c f} (K:Core G S)

-- simple plate maps
@[simp] lemma reaches_zero: K.reachable 0=0:=by
   ext i; unfold reachable; dsimp only; split <;> rfl
def placed : Temps G f→L[ℝ] Dir G f:=LinearMap.toContinuousLinearMap
    { toFun:= K.reachable
      map_add' x y:= by funext i; unfold reachable; dsimp only [Pi.add_apply]; split; simp; rfl
      map_smul' t x:= by funext i; unfold reachable; dsimp only [Pi.smul_apply]; split <;> simp [*]; try rfl }

lemma plates_copy (a:Temps G f): K.seek 1 0 a= represent (K.reachable a):=by
   unfold Core.seek; rw [pull_id]; unfold menu represent; change increment (replica _ (Precision.represent 0)) _=_; rw [link_one,replica_one]
lemma count_root (a:Temps G f) (i:Bond f): collect G (K.reachable a) i =
    if K.snow i then 0 else WithLp.toLp 2 (fun j=>a (i,j)) :=by
   change K.reachable a (Work.E03.poleEquiv f i) = _; unfold reachable snow; rw [Equiv.symm_apply_apply]; dsimp only; split_ifs <;> rfl

-- quote derivative via public prices work.F03 and ours.Plog.
lemma hail (a: Temps G f) (i:Cell f) :
    K.note (1,.inl (i,false)) 0 a = Real.sqrt K.tube.high.direct • Work.F03.faceCurl i (K.reachable a):=by
   let L:=placed K; let F:=fun v:Dir G f=>G.curvature (faceValue (represent v) i); let Y:=Real.sqrt K.tube.high.direct
   have ht : K.jump (1,.inl (i,false)) 0= Y • (F∘ L):=by
     ext1 x; simp only [Core.jump,etched,Bool.false_eq_true,if_false,Sum.elim_inl,plates_copy]; rfl
   have hf: ContDiffAt ℝ ω F (L 0) := by
      rw [map_zero]; exact curvature_diff_mat (fun v=>faceValue (represent v) i) _ (Push.writes ..)
   have hh : DifferentiableAt ℝ (K.jump (1,.inl (i,false)) 0) 0:= by
      rw [ht]; exact ((hf.comp _ L.contDiff.contDiffAt).const_smul Y).differentiableAt (by simp)
   apply HasDerivAt.unique (Push.side _ hh a)
   have he:HasDerivAt (fun t:ℝ=> Y • F (t • L a)) (Y • _) 0:= (Work.F03.curvature_of_hasDerivAt (Work.F03.face_deriv i (L a))).const_smul Y
   rw [ht]; simpa only [Function.comp_apply,Pi.smul_apply,map_smul] using! he

lemma house (h:S.patch.Branches S.kernel G) (a: Temps G f) (i:Bond c) :
    K.note (1,.inr i) 0 a = -Real.sqrt S.kernel.penalty • bills S (K.reachable a) (pole i) := by
   let k:=Push.SectorMeasure.Oriented.choice 1 K.k
   let L:=placed K; let F:=fun v:Dir G f=> G.mat (S.prediction (represent v) k i); let x:= -Real.sqrt S.kernel.penalty
   have he : F 0 = 1 :=by unfold F; rw [link_one,Push.settled S h i k,G.mat_one]
   let A:= fun v:Temps G f=> x • G.plog (F (L v))
   have ha : K.jump (1,.inr i) 0 = A:=by
     ext1 v; simp only [Core.jump,Core.conf,Core.target,Sum.elim_inr,plates_copy,reaches_zero,link_one,Push.settled S h,inv_one,mul_one]; rfl
   have hf : ContDiffAt ℝ ω A 0 := by
      have hq : ContDiffAt ℝ ω F (L 0):= by rw [map_zero]; exact Push.prediction_cont S h i k
      have ht : ContDiffAt ℝ ω G.plog ((F ∘ L) 0):=by rw [comp_apply,map_zero,he]; exact G.plog_diff
      exact ((ht.comp _ (hq.comp _ L.contDiff.contDiffAt)).const_smul x)
   have hQ :=Push.side _ (hf.differentiableAt (by simp)) a; unfold Core.note; rw [ha]; apply hQ.unique
   let y:=bills S (L a) (pole i)
   have hc : HasDerivAt (fun t:ℝ=> F (L (t • a))) (G.colorMat y) 0:= by simp_rw [map_smul]; exact Push.prices S h i k (L a)
   have hd:=((G.plog_diff.differentiableAt (by simp)).hasFDerivAt).comp_hasDerivAt_of_eq (x:=0) hc (by simp only [zero_smul,map_zero,he])
   exact (hd.congr_deriv (Place.plog_velocity ..)).const_smul x

omit K in
lemma ballast_pos :0< ballast := Real.sqrt_pos.mpr (inv_pos.mpr (by exact_mod_cast Fintype.card_pos))

def bulk (K : Core G S) (x:Dir G f) := K.tube.high.direct* (∑ i:Body 2 f, ‖dColor G f 1 x i‖^2) + S.kernel.penalty *
   ∑ i : Body 1 c, ‖bills S x i‖^2



def marine (x:Temps G f): ℝ:= ∑ i: Bond f, ‖(collect G (K.reachable x)) i‖^2

lemma split_book (x:Temps G f): dotProduct x x = marine K x + dotProduct x (K.freeze x) ∧ 0 ≤ dotProduct x (K.freeze x):= by
   have he (i:Bond f):∑ j:G.ColorIndex,x (i,j)*x (i,j) = ‖(collect G (K.reachable x)) i‖^2 + ∑ j:G.ColorIndex,x (i,j)*K.freeze x (i,j):=by
     rw [count_root]; unfold Core.freeze; split_ifs<;> rename_i ht
     · simp
     rw [EuclideanSpace.real_norm_sq_eq]; simp [pow_two]
   refine ⟨?_,Finset.sum_nonneg fun i _=>?_⟩
   · unfold dotProduct marine Acres; rw [Fintype.sum_prod_type,Fintype.sum_prod_type (fun i:Acres f G=>x i*K.freeze x i),←Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun a _=>he a
   unfold Core.freeze; split <;> simp [mul_self_nonneg]

lemma initial (h:S.patch.Branches S.kernel G) (x:Temps G f): ballast^2*bulk K (K.reachable x) + dotProduct x (K.freeze x) ≤ dotProduct x ((K.Gram 0).mulVec x):=by
   unfold Core.Gram; rw [Matrix.add_mulVec, dotProduct_add,K.fires_mul,←Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec _ ((K.D 0).transpose), Matrix.vecMul_transpose];
   apply add_le_add_left
   let CL (a:Drops c f):= ∑ j:G.ColorIndex, (ballast*K.note a 0 x j)^2
   have he(a:Drops c f) : CL a=ballast^2 * ‖K.note a 0 x‖^2:=by unfold CL; simp_rw [mul_pow,← Finset.mul_sum, EuclideanSpace.real_norm_sq_eq]
   have hc(a): 0≤CL a:=by rw [he]; positivity
   let w:= (K.reachable x)
   let u(i:Cell f):=CL (1,.inl (i,false))
   let v(i:Bond c):=CL (1,.inr i)
   have hx(i):u i=ballast^2*(K.tube.high.direct*‖Work.F03.faceCurl i w‖^2):=by
      unfold u; rw [he,hail K,norm_smul,Real.norm_of_nonneg (Real.sqrt_nonneg _),mul_pow,Real.sq_sqrt K.tube.high.quadratic_pos.le]
   have hv(i):v i=ballast^2*(S.kernel.penalty*‖bills S w (pole i)‖^2):=by
      unfold v; rw [he,house K h,norm_smul,norm_neg,Real.norm_of_nonneg (Real.sqrt_nonneg _),mul_pow,Real.sq_sqrt S.kernel.penalty_pos.le]
   have ht : (∑ i,u i)+(∑ i, v i) = ballast^2*bulk K w:=by
      simp_rw [hx,hv]; unfold bulk; simp_rw [← Finset.mul_sum]; rw [mul_add]; congr 2
      · rw [← Equiv.sum_comp (Equiv.prodCongr (Equiv.refl (Site f)) plaqEquiv)]; rfl
      rw [← Equiv.sum_comp (Equiv.prodCongr (Equiv.refl (Site c)) axisEquiv)]; rfl
   rw [←ht]; unfold dotProduct; simp_rw [K.D_mul,←pow_two]; change _≤∑ i:Seats G c f,_
   unfold Seats; rw [Fintype.sum_prod_type (fun i : Seats G c f=> (ballast * K.note i.1 0 x i.2)^2)]; change _≤∑ i:Drops c f,CL i; unfold Drops; rw [Fintype.sum_prod_type CL]
   refine le_trans ?_ (Finset.single_le_sum (s:=Finset.univ) (f:=fun i:Signed=>∑ j:(Twin f⊕ Bond c), CL (i,j)) (fun i _=> Finset.sum_nonneg fun j _=>hc _) (Finset.mem_univ 1))
   rw [Fintype.sum_sum_type]; apply add_le_add_left; unfold Twin; rw [Fintype.sum_prod_type (fun i:Twin f=> CL (1,.inl i))]
   exact Finset.sum_le_sum fun i _=>Finset.single_le_sum (s:=Finset.univ) (f:=fun j:Bool=>CL (1,.inl (i,j))) (fun j _=>hc _) (Finset.mem_univ false)

open Pressure

/-- True lambda0 fixed-L before cutting order R and mask decisions.
General for all plants, any actual Branch on larger geometry. -/
theorem hills (G : Gauge) (L:Side) (J:ℕ) (κ:KernelChoices) (c₀:Clip) : ∃ t:ℝ, 0<t ∧
    ∀ (c f:Side) (S:StepData c f) (K:Core G S), Bid.Larger (G:=G) S → S.kernel=κ → S.patch.L=L → S.patch.J=J → K.tube.high=c₀ →
      Progress.StationaryScenes.Green.Bottom (K.Gram 0) t := by
   obtain ⟨C,hC,h⟩:= Work.E02.answer G L J κ
   let X:=box ((J+3)*L.val+4*L.val); let a:=curlFactor L X C; let b:=probeFactor L
   have ha : 0≤a:=by unfold a curlFactor; positivity
   have hb : 0≤b:=by unfold b probeFactor; positivity
   let e:=ballast^2; have he:0<e:=pow_pos ballast_pos _
   let v:= (min c₀.direct κ.penalty)/(1+a+b); let t:=min 1 (v*e)
   have hv:0<v:=div_pos (lt_min c₀.quadratic_pos κ.penalty_pos) (by positivity)
   have hT:0<t:=lt_min one_pos (mul_pos hv he)
   have hl : v*a ≤ c₀.direct ∧ v*b ≤ κ.penalty:= by
      have h : v*(1+a+b)=min c₀.direct κ.penalty := div_mul_cancel₀ _ (by positivity)
      exact ⟨((mul_le_mul_of_nonneg_left (by linarith) hv.le).trans_eq h).trans (min_le_left ..),((mul_le_mul_of_nonneg_left (by linarith) hv.le).trans_eq h).trans (min_le_right ..)⟩
   refine ⟨t,hT,fun c f S K hs hk hx hj hr p=>?_⟩
   let A:= K.reachable p; let P:=∑ i:Body 2 f,‖dColor G f 1 A i‖^2; let Q:=∑ i : Body 1 c, ‖bills S A i‖^2
   have hp:marine K p ≤ a*P + b*Q := by --namespace
      have h0 : ∀ i : Bond f, i∈K.tree.trunks → collect G A i=0:=fun i hi=>by rw [show collect G A i=_ from count_root K p i,if_pos (show K.snow i from hi)];
      have hc (i:Bond f):= Work.F01.link_bound S hs.1 K.tree K.k A h0 C hC.le i (fun U hu hv=> h c f S hk hx hj hs.2.1 hs.2.2 _ _ hu _ _ _ hv)
      unfold a b P Q; rw [show X=box (macroR S.patch) from by unfold X macroR Patch.radius; rw [hj,hx],show L=S.ratio.count from hx.symm]
      exact sum_estimate S.ratio (box (macroR S.patch)) _ _ (fun i=> ‖collect G A i‖) C (fun i=> norm_nonneg _) hc
   obtain ⟨hr',hd⟩:=split_book K p
   have hA : (v*e)*marine K p ≤ ballast^2 * bulk K A:=by
      have hP:0≤P:=by unfold P; positivity
      have hQ:0≤Q:=by unfold Q; positivity
      unfold bulk; rw [hr,hk,mul_comm v,mul_assoc]
      apply mul_le_mul_of_nonneg_left _ he.le
      apply (mul_le_mul_of_nonneg_left hp hv.le).trans
      rw [mul_add,←mul_assoc,←mul_assoc]; exact add_le_add (mul_le_mul_of_nonneg_right hl.1 hP) (mul_le_mul_of_nonneg_right hl.2 hQ)
   apply le_trans _ (initial K hs.1 p); rw [hr',mul_add]
   exact add_le_add ((mul_le_mul_of_nonneg_right (show t≤v*e from min_le_right ..) (by unfold marine; positivity)).trans hA)
     (mul_le_of_le_one_left hd (min_le_left ..))
end YM.Planned.PrimaryIntegral295.Bosom
