import YM.RG08.Rudder.Proofing

/-!
# Load coherent cover tensors into a Hilbert strip. Scores may shrink by fixed arity at
most, constants in common before mesh/cutoff. The square space is ONLY for aperture
selection; exported law uses Held (full ℓ¹ exponential bill), not ℓ².
-/
noncomputable section
namespace YM.RG08.Rudder
open scoped lp Topology BigOperators Classical ENNReal
open Forms Packets Finset Function Lattice Pert.Bulk
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
variable {I:Type}{n:ℕ}{i:Fin n}{F:Flake n (Market I)}{σ B:ℝ}

abbrev Pin (I:Type){n:ℕ}(i:Fin n):= {x:Tape n (Market I)//(x i).1=0}

abbrev Shelf (I:Type){n:ℕ}(i:Fin n):=ℓ²(Pin I i,ℝ)

def fasten (i:Fin n)(x:Tape n (Market I)):Pin I i :=⟨sway (-((x i).1)) x,by simp [sway,pass]⟩
lemma fasten_sway (X : Tape n (Market I))(a:Cover):fasten i (sway a X)=fasten i X:=by
 apply Subtype.ext;change sway _ (sway a X)=sway _ X;rw [sway_sway];congr 1;change -((X i).1+a)+a=-_;abel
lemma dim_sway (p:Cover)(x:Tape n (Market I)):dim n I σ (sway p x)=dim n I σ x:=by
 unfold dim
 rw [sway,Ground.radius_map (d:=carpet I)]
 intro a b; exact sep_shift ..
lemma dim_pos (x:Tape n (Market I)): 0<dim n I σ x:=Real.exp_pos _

def scrawl (σ:ℝ)(F:Flake n (Market I))(x:Pin I i):=F x.val*dim n I σ x.val

def caddy (i:Fin n)(σ:ℝ):(↥(Shelf I i)) →L[ℝ] Flake n (Market I) := ContinuousLinearMap.pi (fun x=> (dim n I σ x)⁻¹ • lp.evalCLM ℝ _ 2 (fasten i x))
lemma caddy_apply (f:Shelf I i)(x:Tape n (Market I)):caddy i σ f x=(dim n I σ x)⁻¹*f (fasten i x):=rfl
lemma caddy_cohort (f:Shelf I i):Cohort (caddy i σ f):=fun a x=>by rw [caddy_apply,caddy_apply,fasten_sway,dim_sway]
lemma caddy_point (f:Shelf I i)(x:Tape n (Market I)): |caddy i σ f x| * dim n I σ x ≤ ‖f‖:=by
 rw [caddy_apply, abs_mul,abs_of_nonneg (inv_nonneg.mpr (dim_pos _).le),mul_comm,←mul_assoc,mul_inv_cancel₀ (dim_pos _).ne',one_mul];exact lp.norm_apply_le_norm (by norm_num:(2:ℝ≥0∞)≠0) f _ -- abs needs Real.norm

lemma doubleReal : (2:ℝ≥0∞).toReal=(2:ℝ):=by simp
lemma squareReal (a:ℝ):a^(2:ℝ≥0∞).toReal=a^(2:ℕ):=by rw [doubleReal]; norm_cast

variable [Fintype I]
private lemma pinned (h:Held (carpet I) σ B F)(hb:0≤B)(s:Finset (Pin I i)) :
    ∑ x∈s, |scrawl σ F x| ≤ Fintype.card I * B:=by
 let a(t:Tape n (Market I)):=|F t| *dim n I σ t
 let S:=s.image Subtype.val
 have he(x:Pin I i):|scrawl σ F x|=a x.val:=by simp only [scrawl,abs_mul,abs_of_nonneg (dim_pos _).le,a]
 simp_rw [he, ← Finset.sum_image (f:=a) (s:=s) (g:=Subtype.val) (by exact fun x _ y _ h=>Subtype.ext h)] -- ?
 calc
  _ ≤ ∑ x∈S,∑ j:I,if x i=(0,j) then a x else 0:=sum_le_sum fun x hx=>?_
  _ = ∑ j:I,∑ x∈S, if x i=(0,j) then a x else 0:=sum_comm
  _ ≤ _:=by
    rw [show (↑(Fintype.card I):ℝ)*B=∑ _:I,B by simp];apply sum_le_sum;intro j _
    have hh:= (Ticket.gives h hb (i,(0,j)))
    have hg(t:Tape n (Market I)): (if t i=(0,j) then a t else 0) = ‖hung F (i,(0,j)) t‖ * Real.exp (Forms.hike (carpet I) n σ (i,(0,j)) t):=by
        unfold a hung;split_ifs <;>rename_i hp <;> simp [dim,Forms.hike, *] at *
    simp_rw [hg]; exact (hh.2.1.sum_le_tsum S (fun i _=>hh.1 i)).trans hh.2.2
 obtain ⟨x,hx,rfl⟩:=mem_image.mp hx
 have ht:x.val i=(0,(x.val i).2):=Prod.ext x.property rfl
 refine le_trans (le_of_eq (Eq.symm (if_pos ht))) (Finset.single_le_sum (f:=fun j:I=> if x.val i=(0,j) then a x.val else 0) ?_ (mem_univ _))
 intro j _;split_ifs; · exact mul_nonneg (abs_nonneg _) (dim_pos _).le
 exact le_refl _

private lemma pin_pay (h:Held (carpet I) σ B F)(hb:0≤B)(s:Finset (Pin I i)) :
 ∑ x∈s,‖scrawl σ F x‖ ^ (2:ℝ≥0∞).toReal ≤ (Fintype.card I * B)^ (2:ℝ≥0∞).toReal:=by
 simp_rw [squareReal, Real.norm_eq_abs];have he:=pinned h hb s
 calc
 _ ≤ (∑ x∈s,|scrawl σ F x|)^2:=by
    simp_rw [pow_two,Finset.sum_mul];apply sum_le_sum;intro x hx
    gcongr;exact Finset.single_le_sum (f:=fun x=> |scrawl σ F x|) (fun i _=>abs_nonneg _) hx
 _ ≤ (↑(Fintype.card I)*B)^2:=by gcongr

lemma loads (h:Cohort F)(H:Held (carpet I) σ B F)(hb:0≤B):∃ f:Shelf I i, caddy i σ f=F ∧ ‖f‖≤ Fintype.card I*B:=by
 let f:Shelf I i:=⟨scrawl σ F,memℓp_gen' (pin_pay (i:=i) H hb)⟩
 refine ⟨f,funext fun x=> ?_,lp.norm_le_of_forall_sum_le (by rw [doubleReal];norm_num) (by positivity) (pin_pay H hb)⟩
 change _⁻¹ * (F (sway _ x)*dim _ _ _ (sway _ x)) = _
 rw [dim_sway,h,mul_comm (F _),←mul_assoc,inv_mul_cancel₀ (dim_pos _).ne',one_mul]
end YM.RG08.Rudder
