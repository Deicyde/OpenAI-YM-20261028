import YM.MergeProof.West.Sally
import YM.MergeProof.West.Stencil
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Ribbons
open Filter Set Function MeasureTheory Analysis Extraction Table Ward Climb Cells Next.UVStress Wilson Lattice Around Accent
open scoped Topology ContDiff BigOperators Classical
variable {G:Gauge}{C:Family G}{F:Extraction.Order}{S:Table C.book}{n:ℕ}
variable {W:DiffPlan S}{ι:Type*}[Fintype ι](I:Watch C)
set_option quotPrecheck false
local notation "R" => fun i:ℕ=> fuga C.path.levels (i+1)
lemma insideW (he:Note C.S (R) (-1)) :∀ᶠ m in atTop,∀ y∈ arena ((R) m), slide C.S (m+1) (Points.cons y I.held):=by
  have hsh:Tendsto (fun m:ℕ=>4*C.S.a (m+1)) atTop (𝓝 0):=by simpa using (C.S.shrinks.comp (tendsto_add_atTop_nat 1)).const_mul (4:ℝ)
  have ht:Tendsto (fun m=>4*C.S.a (m+1)+4*(R) m) atTop (𝓝 0):= by simpa only [mul_zero,zero_add] using hsh.add ((he.thins (by norm_num)).const_mul (4:ℝ))
  have hx (i:Fin I.n): 0< ‖I.held i.succ‖:= norm_pos_iff.mpr (fun h=>Fin.succ_ne_zero _ (I.distinct (h.trans I.origin.symm)))
  let Z := {p:Fin (I.n+1) × Fin (I.n+1)//p.1≠p.2}
  filter_upwards [eventually_all.mpr (fun i:Z=> hsh.eventually (gt_mem_nhds (norm_pos_iff.mpr (sub_ne_zero.mpr (I.distinct.ne i.property))))), eventually_all.mpr fun i=>ht.eventually (gt_mem_nhds (hx i))] with m hp hv y hy
  let hI := ((C.path.levels.budget (m+1)).B:ℝ)
  have hP: (1:ℝ) ≤ hI := by unfold hI; exact_mod_cast (show 1≤(C.path.levels.budget (m+1)).B from (C.path.levels.budget _).B_pos)
  have hm: (R) m /16 ≥ 4*C.S.a (m+1):=by
      change (R) m /16 ≥ _; change 128*hI^2*C.S.a _/16 ≥ _; have HH:=mul_le_mul_of_nonneg_right (show 4 ≤ 8*hI^2 by nlinarith) (C.S.a_pos (m+1)).le; linarith
  have hY(i:Fin (I.n+1)):4*C.S.a (m+1)< ‖I.held i-y‖:=by
     refine Fin.cases (by simpa [I.origin] using hm.trans_lt hy.1) (fun i=>?_) i
     linarith only [hv i,norm_le_insert' (I.held i.succ) y, hy.2]
  intro i j
  refine Fin.cases ?_ (fun i=>?_) i
  · refine Fin.cases ?_ (fun l=>?_) j
    · simp
    intro _; simpa [Points.cons] using hY l
  refine Fin.cases ?_ (fun l=>?_) j
  · intro _; simpa [Points.cons,norm_sub_rev] using hY i
  intro hl; simpa only [Points.cons,points_apply,Fin.cons_succ] using hp (⟨(l,i),fun h=>hl (congrArg Fin.succ h.symm)⟩:Z)
where
 norm_le_insert' (v w:E4):‖v‖ ≤ ‖v-w‖+ ‖w‖ := by simpa [add_comm,norm_sub_rev] using norm_le_insert w v

lemma Note.longer {f}{s} (he:Note C.S f s)(l:ℕ):Note C.S (fun i=>f (i+l)) s:=by
   induction l with
   | zero=>exact he
   | succ l ih=>
       convert ih.scales C.path.levels.fits.mesh using 1; ext; congr 1; omega

def Clouds (q:Fin n→ C.book.Token):ℕ:=∑ i:Fin n, ((q i).1+2)
lemma Note.glory (q:Fin n→ S.Tag): Note C.S (honor C.S (expose ∘ q)) (Clouds (C:=C) (expose ∘ q)):= by
   convert Note.bell_exp C.S (Clouds (C:=C) (expose ∘ q)) using 1; ext1 i; unfold honor Clouds
   push_cast; rw [Finset.sum_mul,Real.exp_sum]
variable (w:Fin (I.n+1)→ S.Tag) (q:S.Tag)(D:ℕ)
lemma beneath (he:Note C.S (R) (-1)) (hC:C.Makes)(hq:Cells.CellHyp C F)(ho:F.PointLimits C S)(H:S.Hierarchy) (t:ℝ)(j:ℕ→ℕ) (hj:Tendsto j atTop atTop)(hJ:Tendsto (fun i:ℕ=>C.S.scale (j i)/C.S.scale i) atTop (𝓝 t)) (hp: q.fst+2+(Clouds (C:=C) (expose ∘ w):ℝ)<(D:ℝ)*t) {ε:ℝ}(hE:0<ε):
   ∀ᶠ i in atTop, ∀ y∈arena ((R) i), (C.S.a (j i))^D * ‖disc (Fin.cons (α:=fun _=>S.Tag) q w) (Points.cons y I.held)‖ ≤ ε:=by
   obtain ⟨l,hl⟩:= exists_nat_gt (((I.n+2:ℕ):ℝ)*6)
   let u := Fin.cons (α:=fun _=>S.Tag) q w
   have hT:(Clouds (C:=C) (expose ∘ u):ℝ)+ D*((-1)*t)<0:=by
      have hm:Clouds (C:=C) (expose ∘ u)= q.1+2+Clouds (C:=C) (expose ∘ w):=by
          change (∑ i:Fin (I.n+2),_)=_; rw [Fin.sum_univ_succ]; dsimp only [Clouds,comp_apply,u,Fin.cons_succ,Fin.cons_zero]; rfl
      rw [hm]; push_cast; linarith
   have hz:= (Note.mills (Note.longer (C:=C) (Note.glory (C:=C) u) (l+1)) (((Note.note_a C.S).relay j hj hJ).powerN D)).thins hT
   filter_upwards [(tendsto_add_atTop_nat 1).eventually (maine hC hq ho H (q:=u) l hl),insideW I he, hz.eventually (ge_mem_nhds hE)] with i hi hk hh y hy
   refine (mul_le_mul_of_nonneg_left (hi _ (hk y hy)) (pow_nonneg (C.S.a_pos _).le D)).trans ?_
   change C.S.a (j i)^D*honor C.S (expose∘u) (i+1+l) ≤ _; rw [show i+1+l=i+(l+1) by omega, mul_comm];exact hh
end YM.MergeProof.Ribbons
