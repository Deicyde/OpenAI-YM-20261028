import YM.RG08.Rudder.Sym.Seats
import YM.RG08.Rudder.Loop.Empty

/-!
# Color subspaces: lift respects joint invariants. No coefficient convention needed here
apart from submodule of the actual color arrays, applies for tensors of real YM colors.
-/
noncomputable section
namespace YM.RG08.Rudder.Symmetry
open scoped Topology BigOperators Classical ENNReal
open Forms Packets Finset Function Lattice Pert.Bulk Exterior Laurent AnalyticNext.QuarticMatch.BoxChain
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
variable {I:Type}{n:ℕ}{F:Raw I n}

abbrev Urn (I:Type)(n:ℕ):=Tape n I→ℝ
def hat (F:Raw I n)(x:Tape n (Market Tablet)):Urn I n:=fun y=>hum F y x
def hue (V:Submodule ℝ (Urn I n))(F:Raw I n):Prop := ∀ x,hat F x∈V

def applyHue (U:Urn I n→ₗ[ℝ] Urn I n):Raw I n→ₗ[ℝ] Raw I n where
 toFun F:=joinC (fun y x=>U (hat F x) y)
 map_add' f g:=by ext x;let v(i:Fin n):=((x i).1,(x i).2.1);let z(i:Fin n):=(x i).2.2;exact congrFun (U.map_add (hat f v) (hat g v)) z
 map_smul' a f:=by ext x; let v(i:Fin n):=((x i).1,(x i).2.1);let z(i:Fin n):=(x i).2.2;exact congrFun (U.map_smul a (hat f v)) z
lemma applies (U:Urn I n→ₗ[ℝ] Urn I n)(x:Tape n (Market Tablet)) : hat (applyHue U F) x=U (hat F x):=rfl
lemma complete (U:Urn I n→ₗ[ℝ] Urn I n){V:Submodule ℝ (Urn I n)}(h:LinearMap.range U≤V): hue V (applyHue U F):=fun x=>by rw [applies];exact h (LinearMap.mem_range_self U _)

def ignored (V:Submodule ℝ (Urn I n)):= V.exists_isCompl.choose
def fix (V:Submodule ℝ (Urn I n)):= V.subtype.comp (Submodule.projectionOnto V (ignored V) V.exists_isCompl.choose_spec)
lemma hue_fixed (V:Submodule ℝ (Urn I n))(h:hue V F):applyHue (fix V) F=F:=by
 ext x;let v(i:Fin n):=((x i).1,(x i).2.1);let z(i:Fin n):=(x i).2.2
 exact congrFun (show fix V (hat F v)=hat F v from by simp [fix, h v]) z
lemma fixed_hue (V:Submodule ℝ (Urn I n)): hue V (applyHue (fix V) F):=complete _ (by rintro _ ⟨x,rfl⟩;exact Submodule.coe_mem _)

lemma hat_here {r:Fin n→ℕ}(h:Graded F r){x:Tape n (Market Tablet)}{i:Fin n}(he:(x i).2.card≠r i):hat F x=0:=funext fun y=>h y i x he
lemma applyHue_grade {U:Urn I n→ₗ[ℝ] Urn I n}{r:Fin n→ℕ}(h:Graded F r):Graded (applyHue U F) r:=by intro y i x he;change U (hat F x) y=_; rw [hat_here h he,map_zero];rfl
lemma hat_path (h:Cohort F)(v:Cover)(x:Tape n (Market Tablet)):hat F (sway v x)=hat F x:=funext fun y=>h v (lyre x y)
lemma applyHue_path {U:Urn I n→ₗ[ℝ] Urn I n}(h:Cohort F):Cohort (applyHue U F):=by
 intro a x;let v(i:Fin n):=((x i).1,(x i).2.1);let z(i:Fin n):=(x i).2.2;change U (hat F (sway a v)) z=U (hat F v) z;rw [hat_path h]

lemma hat_border (x:Tape n (Market Tablet))(j):hat (boundary j F) x=∑ i:Axis,if i∈ (x j).2 then 0 else sign (x j).2 i •
      ((hat F (update x j ((x j).1-step i,insert i (x j).2))) - hat F (update x j ((x j).1,insert i (x j).2))):=by
 ext y;change (lower j (hum F y)) x=_;rw [lower_at,Finset.sum_apply];apply sum_congr rfl; intro i _;rw [sect_at];split_ifs<;>rfl
lemma boundary_hue (U:Urn I n→ₗ[ℝ] Urn I n)(j):boundary j (applyHue U F)= applyHue U (boundary j F):=by
 funext x;let v(i:Fin n):=((x i).1,(x i).2.1);let z(i:Fin n):=(x i).2.2
 change hat (boundary j _) v z=U (hat (boundary j F) v) z
 rw [hat_border,hat_border,map_sum]; simp only [applies, apply_ite U,map_zero,map_smul,map_sub]
lemma picture_hue (U:Urn I n→ₗ[ℝ] Urn I n):picture I n (applyHue U F)= applyHue U (picture I n F):=by -- picture I actually takes Tone I; ok
 have he (s:List (Fin n))(F:Raw I n):patchL s (applyHue U F)=applyHue U (patchL s F):=by
    induction s generalizing F with
    | nil=>rfl
    | cons j t ih=>change patchL t (boundary _ _)= applyHue U (patchL t (boundary j F)); rw [boundary_hue, ih]
 exact he ..

lemma hue_card (s:Signed){V:Submodule ℝ (Urn I n)}(h:hue V F):hue V (orbit s F):=by
 intro x
 let f:Market Tablet→Market Tablet:=fun x=>(s.act x.1+evil s x.2,marks s x.2)
 let c:ℝ:=∏ i,toll s (x i).2
 exact V.smul_mem c (h (f ∘ x))
lemma canopy_hue {V:Submodule ℝ (Urn I n)}(h:hue V F):hue V (canopy I n F):=by
 intro x;rw [canopy_apply]
 change (groupcard⁻¹ • (hat (∑ s:Signed,orbit s F) x))∈V
 have he:hat (∑ s:Signed,orbit s F) x=∑ s:Signed,hat (orbit s F) x:=by ext y;simp [hat,hum,Finset.sum_apply]
 rw [he];exact V.smul_mem _ (sum_mem (fun s _=>hue_card s h x)) -- sum_mem?

def adjGrade (V:Submodule ℝ (Urn I n)):Prop:=∀ ξ:Equiv.Perm (Fin n),∀ f∈V,(fun x=>f (x ∘ ξ)) ∈V
lemma bleach_hue {V:Submodule ℝ (Urn I n)}(hV:adjGrade V)(h:hue V F):hue V (bleach F):=by
 intro x
 let c:= (Fintype.card (Equiv.Perm (Fin n)):ℝ)⁻¹
 have he:hat (bleach F) x=c • ∑ ξ:Equiv.Perm (Fin n),hat (woven F ξ) x:=by ext y; simp [hat,hum,c,bleach,Finset.sum_apply]
 rw [he];apply V.smul_mem;apply sum_mem;intro ξ _; exact hV ξ _ (h (x ∘ ξ))

variable [Fintype I]
def fixedFare (U:Urn I n→ₗ[ℝ] Urn I n):ℝ:= ∑ y:Tape n I,∑ w:Tape n I,|U (Pi.single w 1) y|
lemma fare_pos (U:Urn I n→ₗ[ℝ] Urn I n): 0≤fixedFare U:=sum_nonneg fun _ _=>sum_nonneg fun _ _=>abs_nonneg _
lemma recolor_size (U:Urn I n→ₗ[ℝ] Urn I n){f:Urn I n}{a:ℝ}(ha:∀ x,|f x|≤a)(_ht:0≤a)(y:Tape n I):|U f y|≤fixedFare U*a:=by
 rw [show f=∑ w:Tape n I,f w • (Pi.single w 1) by ext j; simp [Finset.sum_apply,Pi.single_apply,mul_ite]] -- syntax
 rw [map_sum,Finset.sum_apply];simp only [map_smul,Pi.smul_apply,smul_eq_mul];apply (Finset.abs_sum_le_sum_abs _ _).trans
 unfold fixedFare; rw [Finset.sum_comm] -- reorder for each w easier
 rw [Finset.sum_mul]; apply Finset.sum_le_sum;intro w _
 rw [abs_mul,mul_comm];exact mul_le_mul (Finset.single_le_sum (f:=fun z=>|U (Pi.single w 1) z|) (fun _ _=>abs_nonneg _) (mem_univ y)) (ha w) (abs_nonneg _) (by apply sum_nonneg; intros;positivity)
lemma hue_held (U:Urn I n→ₗ[ℝ] Urn I n)(σ B:ℝ)(hp:0<σ)(hb:0≤B)(hn:0<n)(h:Cohort F)(hc:Held (carpet (Tone I)) σ B F): Held (carpet (Tone I)) (σ/2) ((debit' (Tone I) n σ*fixedFare U)*B) (applyHue U F):=by
 have hv:=NextTo.unit hp hb h hc hn
 rw [mul_assoc];apply NextTo.held _ hn (mul_nonneg (fare_pos U) hb) hp
 intro y; refine ⟨?_,hp,mul_nonneg (fare_pos U) hb,?_⟩
 · intro b X;exact applyHue_path (U:=U) h b (lyre X y)
 intro x i j;rw [Real.norm_eq_abs,mul_assoc];change |U (hat F x) y| ≤_;apply recolor_size U _ (mul_nonneg hb (cost_size ..))
 intro z; exact le_trans (by rfl) ((hv z).each x i j)
end YM.RG08.Rudder.Symmetry
