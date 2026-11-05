import YM.Planned.PRIMARY_INTEGRAL_295.Glints
import YM.Push.SECTOR_MEASURE.Oriented




/-!
# Flat Affvd: commuting turns with the actual A0 & station matrices

W.PPX already proved, use covariance from exact family of Flight rows
at SAME K. Pull signs on torus records including negative shift; actual
prediction branch price root-chart derivative. `Sworn` on orientation
(as in Part I). Output-row full formulas here remain WT obligations, used
one at time in next calculation. -/
set_option autoImplicit false
noncomputable section
namespace YM.Planned.PrimaryIntegral295.Bunks
open Function Filter Set Metric
open Labels Lattice RG Wilson Pressure Precision Exterior Tree Streets Carrier Bloch Place Push.SectorMeasure.Oriented
open Bid (pulled bills Sworn)
open Next.Free Matrix
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius RealInnerProductSpace Classical
variable {G : Gauge} {T : Finset Cover} {c f n : Side} {S : StepData c f} (s:Signed)

abbrev faceAlias (n:Side) (u:Bond n):=Work.E03.poleEquiv n u
lemma twisted (p: Bond n) (x:Dir G n) : pulled x s (faceAlias n p)=bias s p.2 • x (faceAlias n (sendEdge s 0 p)):=by
   unfold pulled bias; rw [show (faceAlias n p).2= Exterior.coord p.2 from rfl,show (faceAlias n p).1=p.1 from rfl]; unfold sendEdge
   simp only [show axisEquiv.symm (coord p.2)=p.2 from axisEquiv.symm_apply_apply p.2]; unfold Step.rotate posDir
   rcases H:s.flip p.2 <;> simp only [Bool.false_xor,Bool.false_eq_true,if_false,if_true,neg_smul,one_smul] <;> rfl

lemma scaled (a:Dir G n) (v:ℝ) : pulled (v • a) s=v • pulled a s:=by
   funext i; obtain ⟨p,rfl⟩:= (Work.E03.poleEquiv n).surjective i; rw [Pi.smul_apply,twisted,twisted,Pi.smul_apply]; exact smul_comm ..
lemma combined (a b:Dir G n):pulled (a+b) s=pulled a s+pulled b s:=by
   funext i; obtain ⟨p,rfl⟩:= (Work.E03.poleEquiv n).surjective i; rw [Pi.add_apply,twisted,twisted,twisted,Pi.add_apply,smul_add]
lemma split_cost (a b:Dir G n):pulled (a-b) s=pulled a s-pulled b s:=by
   rw [show pulled a s=pulled ((a-b)+b) s from by rw [sub_add_cancel],combined]; abel

def carried (a b:Dir G n):=∑ i, inner ℝ (a i) (b i)
lemma counter (a b:Dir G n): carried (pulled a s) (pulled b s)=carried a b:=by
   unfold carried; let e:=Work.E03.poleEquiv n
   rw [← e.sum_comp, ← e.sum_comp (fun i=>inner ℝ (a i) (b i)), ← Equiv.sum_comp (StepData.sendBonds s (0:Site n)) (fun j=>inner ℝ (a (e j)) (b (e j)))]
   apply Finset.sum_congr rfl; intro i hi
   change ⟪pulled _ _ (faceAlias n i),pulled _ _ (faceAlias n i)⟫= ⟪a (faceAlias n (sendEdge s 0 i)), b _⟫
   rw [twisted,twisted]; unfold bias; split<;>simp<;>rfl
lemma forwarded : Surjective (fun a:Dir G n=>pulled a s) := by
   intro a
   let e:= Work.E03.poleEquiv n; let v:= StepData.sendBonds s (0:Site n)
   let b(p:Bond n) := bias s p.2 • a (e p)
   refine ⟨fun i=> b (v.symm (e.symm i)),funext fun i=>?_⟩
   obtain ⟨p,rfl⟩:= e.surjective i
   dsimp only; unfold e; rw [twisted]; change bias s p.2 • b (v.symm (e.symm (e (v p))))=_
   rw [Equiv.symm_apply_apply,Equiv.symm_apply_apply]; unfold b bias; split <;> simp <;> rfl

-- sign/small on actual
lemma aboard_move (a:Dir G n) : aboard G n (pulled a s)= Carrier.orient s (aboard G n a) :=by
   funext x i
   change pulled a s (faceAlias n (wrap n x,i)) = bias s i • _
   rw [twisted]; apply congr_arg (bias s i • ·)
   rw [going_spec]; unfold aboard collect sendEdge affine Step.used Step.rotate posDir delay
   simp only [Bool.false_xor,add_zero]
   cases h:s.flip i
   · simp only [Bool.false_eq_true,if_false,add_zero,wrap_signed]; rfl
   simp only [if_true,map_add,map_neg,wrap_step,wrap_signed,sub_eq_add_neg]; rfl

omit s in
lemma aboard_faithful (n:Side):Injective (aboard G n) :=by
   intro a b hx; funext i; obtain ⟨⟨x,i⟩,rfl⟩:= (Work.E03.poleEquiv n).surjective i
   have he:= congr_fun (congr_fun hx (lift x)) i; unfold aboard at he; rw [wrap_lift] at he; exact he

-- supply W.H.strong from record
abbrev Spins (W:Lines S.ratio.count) := ∀ (s:Signed) (b:Dir G c), Streets.pledge (installed S.ratio W) (pulled b s)=pulled (Streets.pledge (installed S.ratio W) b) s
omit s in
lemma capitals {j t} (P:Flight j t) (k:ℝ) (hk:0<k) (ht:4≤t) {W:Lines S.ratio.count}
    (hP:P.L=S.ratio.count) (he:W=(hP ▸ linesOf P k)) (hw:Whole W) : Spins (S:=S) (G:=G) W:=by
   intro s b
   apply aboard_faithful
   rw [aboard_move s, Streets.street S.ratio _ hw,Streets.street S.ratio _ hw,aboard_move s]
   suffices hg : ∀ s (x : Window G.Color),Carrier.applyLine W (Carrier.orient s x) = Carrier.orient s (Carrier.applyLine W x) by exact hg _ _
   have hv : ∀ (L:Side) (h:P.L=L), ∀ (s:Signed) (x:Window G.Color), applyLine (show Lines L from h ▸ linesOf P k) (orient s x)=orient s (applyLine (show Lines L from h ▸ linesOf P k) x) := by
      intro L hl; subst L; exact fun s x => origin_turn s P k hk ht x
   rw [he]; exact hv _ _

-- weighted identity equipment

def land (H:Bed) (a:Dir G n):=Streets.pledge (K (H.metric.acts n)) a
omit s in
lemma weighs (H:Bed) (a b:Dir G n):carried a (land H b)=Bid.gaugeFiscal H a b:=by
   rw [carried,Work.F04.counting_inner]; unfold Bid.gaugeFiscal
   apply Finset.sum_congr rfl; intro i hi
   have hp : parts G 1 (land H b) i= K (H.metric.acts n)*ᵥ parts G 1 b i:= funext fun j=> Streets.code ..
   rw [hp]
lemma swapped (H:Bed) (he:Sworn H n G) (b:Dir G n): pulled (land H b) s=land H (pulled b s):=by
   have h(u : Dir G n):carried u (pulled (land H b) s)=carried u (land H (pulled b s)):=by
      obtain ⟨a,rfl⟩:=forwarded s u; rw [counter,weighs,weighs,he]
   funext i; refine ext_inner_left ℝ (fun x=>?_); have he:=h (Pi.single i x)
   have hv (v:Dir G n):carried (Pi.single i x) v=⟪x,v i⟫ := by
      unfold carried; rw [Finset.sum_eq_single i]; simp; intro j _ hj; simp [hj]; intro H; exact False.elim (H (Finset.mem_univ i))
   rwa [hv,hv] at he

-- Q actual under turn, derive bills formula DIRECT rooted orientation.
lemma pred_fibre (h:S.patch.Branches S.kernel G) (k:S.Choices) (a:Dir G f) :pulled (bills S a) s=bills S (pulled a s):=by
   have he (t:ℝ) := (Push.SectorMeasure.Oriented.carry s h k (represent (t • a))).2
   let b:=pulled a s
   let F(t:ℝ):=S.prediction (represent (t • a)) k; let H(t:ℝ):=S.prediction (represent (t • b)) (Push.SectorMeasure.Oriented.choice s k)
   have hx (t:ℝ): H t=pull s 0 (F t):=by unfold H F b; rw [← Work.F03.represent_pulled, he]
   funext i; obtain ⟨p,rfl⟩:= (Work.E03.poleEquiv c).surjective i
   rw [twisted]; let v:=sendEdge s 0 p
   have hg : HasDerivAt (fun t:ℝ=> G.mat (H t p)) (G.colorMat (bills S b (faceAlias c p))) 0:= Push.prices S h p _ b
   have hf : HasDerivAt (fun t:ℝ=> G.mat (F t v)) (G.colorMat (bills S a (faceAlias c v))) 0:= Push.prices S h v _ a
   have hP (t:ℝ): H t p = if s.flip p.2 then (F t v)⁻¹ else F t v:=by
      rw [hx]; unfold pull Step.rotate posDir Step.read; unfold v sendEdge Step.rotate posDir; simp only [Bool.false_xor]
   simp_rw [hP] at hg; apply G.colorMat_injective; unfold bias; cases hh:s.flip p.2
   · simp only [hh,Bool.false_eq_true,if_false,one_smul] at hg ⊢; exact hf.unique hg
   simp only [hh,if_true,G.mat_inv,neg_smul,one_smul,map_neg] at hg ⊢; exact (G.colorMat_skew (bills S a (faceAlias c v))).symm.trans (hf.star.unique hg)

-- graded comm maps soap of curls
lemma colored_turn (a:Dir G n) (k:G.ColorIndex) : parts G 1 (pulled a s) k=Next.Free.reorient s (parts G 1 a k):=by
   unfold Bid.pulled parts Next.Free.reorient; funext i; dsimp only; split <;> rfl
end YM.Planned.PrimaryIntegral295.Bunks
