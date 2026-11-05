import YM.MergeProof.Weathervane
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof
open Finset Function Filter MeasureTheory Lattice Wilson RG Source Labels Extra.Histories
open Planned.GuardedAtom Push Local Motion
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {G:Gauge}{n:Side}{ι:Type*}{d:ℕ}{F:Labels.Frame G d}{o:Site n}
    {R:Rep G n}{P:BudgetPoint}(m j:Motion)
-- action reduction on Motion.either. needed on apron
private def glide (t:Signed):Motion≃Motion:=(Equiv.mulLeft t).prodCongr (Equiv.refl _)
def twist (t a:Motion):Motion:=(t.1*a.1,Bool.xor t.2 a.2)
def bal (t:Motion): Motion ≃ Motion where
   toFun:= twist t
   invFun:=twist (Motion.backward t)
   left_inv j:= by rcases t with ⟨t,_|_⟩ <;>cases j.2 <;>simp [twist,Motion.backward]
   right_inv j:= by rcases t with ⟨t,_|_⟩ <;>cases j.2 <;>simp [twist,Motion.backward]
-- simplify patch compositions
local notation "D" => Motion.patch F
variable (v:F.Coeff)
lemma opus : D m (D j v)=D (twist m j) v:=by
   rcases m with ⟨t,_|_⟩ <;> rcases j with ⟨u,_|_⟩<;> simp [Motion.patch,twist,(act_conj F), ← Frame.act_mul, show ∀ t u:Signed,(t*u).ortho=t.ortho*u.ortho from fun t u=> map_mul Signed.inclusionO t u]
lemma oper (a:ℂ): Motion.scalar m (Motion.scalar j a)= Motion.scalar (twist m j) a:= by rcases m with ⟨_,_|_⟩<;> rcases j with ⟨_,_|_⟩<;>simp [Motion.scalar,twist]
-- floatUp composition
local notation "xo"=> (0:Site n)
lemma up_twice (p:Support n): sky m xo (sky j xo p)= sky (twist m j) xo p:= by
   simp only [shading,image_image]; refine image_congr (fun i _=>?_); change affine m.1 xo (affine j.1 xo i)=affine (twist m j).1 xo i; simp [affine,twist,Signed.act_mul]
lemma tow (p : Box n): puff m xo (puff j xo p)= puff (twist m j) xo p:= Prod.ext (up_twice m j p.1) (up_twice m j p.2)
lemma climbs (f:Box n→Config G n→ℂ): floatUp m xo (floatUp j xo f)=floatUp (twist m j) xo f:=by
   funext p U; obtain ⟨p,rfl⟩:= (puff (twist m j) xo).surjective p
   unfold floatUp stepUp; rw [(puff (twist ..) xo).symm_apply_apply,← tow, Equiv.symm_apply_apply,Equiv.symm_apply_apply]
   simp_rw [pull_pull,oper]; simp [affine,twist] -- order
lemma pipes (g:ι→ℂ)(b:Finset ι): Motion.scalar m (∑ i∈b,g i)=∑ i∈b,Motion.scalar m (g i):=by unfold Motion.scalar;split_ifs; exact star_sum ..; rfl
lemma trove (i:F.Index): scalar m (chips F v (j,i)) = chips F (D m v) (twist m j,i):= by
   let t:= twist m j; let j':= backward j; let v':= (D) j' v
   have hp : D (backward t) (D m v)= v':= Motion.patch_inj F t (by rw [round]; exact (show D m v=D t v' from by rw [← opus,round]))
   rw [chips,show (twist m j,i)= (t,i) from rfl]; change scalar m (_ * scalar j _)=(_ * scalar t _); rw [hp]; simp_rw [scalar_mul,oper]; congr 1; apply scalar_real
set_option maxRecDepth 4000 in
lemma concert (Q:F.Index→ Box n→ Config G n→ℂ): let O(p:Tally F):= floatUp p.1 xo (Q p.2)
    let E(x):=∑ p:Tally F, chips F x p • O p
    floatUp m xo (E v)= E (D m v):= by
   intro O E; let e:= Equiv.prodCongr (bal m) (Equiv.refl F.Index); funext i U; unfold E; -- rw RHS
   unfold floatUp stepUp; simp_rw [Finset.sum_apply, pipes]; nth_rw 2 [← Equiv.sum_comp e]; refine Finset.sum_congr rfl fun j _=> ?_
   change scalar m (chips F v j * _)= chips F (D m v) _ * _
   rw [scalar_mul,show j= (j.1,j.2) from rfl, trove]
   exact congr_arg (_ * ·) (congr_fun (congr_fun (climbs m j.1 (Q j.2)) _) _) -- check
variable {H:Hol G}{T:SectionData F} (p: Coefficient F n) (x:Site n)(h:T.Sound H) (π : R.activities.Moves m.1 x)
include h
lemma bow : (audition π p).exponentialEntry (affine m.1 x o) T R=stepUp m x (p.exponentialEntry o T R):=by
   let V:=affine m.1 x o; let t:=m.1
   have hi:(reorient π p).exponentialEntry V T R=p.exponentialEntry o T R ∘ pull t x:=by
      funext U; let v:=pull t x U;have he := footprint_turn h t o x
      have hP q : T.places q o ∘ pull t x = T.places (F.act t.ortho q) (affine t x o) := funext fun V => T.placed_signed h t o x q V
      unfold Coefficient.exponentialEntry Coefficient.maskedTerm reorient V t at *; dsimp only [Function.comp_apply]; rw [act_at_zero, ← core_act, F.scaling, he, masked_pull, hP]; simp_rw [masked_pull]; rfl
   let P:=reorient π p
   have hY U : (barAll P).exponentialEntry V T R U = star (P.exponentialEntry V T R U) := by
      have hb (i): (barAll P).maskedTerm R i U = star (P.maskedTerm R i U) := masked_bar ..
      rw [Coefficient.exponentialEntry,Coefficient.exponentialEntry, star_add,star_add,tsum_star]
      simp_rw [hb,barAll,Pi.star_apply]; rw [core_star,scaled_star,show T.places (star (F.scaled R.p.threshold⁻¹ (F.core P.x))) V = star (T.places (F.scaled R.p.threshold⁻¹ (F.core P.x)) V) from funext fun _ => h.ordinary_real ..,masked_bar]
   funext U; unfold audition stepUp Motion.scalar; split; exact (hY U).trans (congr_arg star (congr_fun hi U)); exact congr_fun hi U
-- any Heard invariant via orientation.profile and density! ledger primary.exp linear
omit v h π x m in
lemma expoLinear (P : F.Coeff→ Coefficient F n)(t:F.Coeff→ℝ){s:ℝ}(h:Ledger F n P)(he:∀ v,(P v).remBound o R s (t v)):IsLinearMap ℂ fun v=> (P v).exponentialEntry o T R:=by
  let f x j V:= (P x).maskedTerm R j V
  have hf v U: Summable fun j=> f v j U:=(Coefficient.regular_series (he v)).summable U
  have hv j V: IsLinearMap ℂ (fun x=> f x j V):=by
     unfold f Coefficient.maskedTerm; simp_rw [h.tags]; constructor
     · intro x y; rw [h.reg.map_add]; exact congr_fun (map_add (maskLinear R.p.threshold _) _ _) V -- implicit
     intro c x; rw [h.reg.map_smul]; exact congr_fun (map_smul (maskLinear R.p.threshold _) _ _) V
  constructor
  · intro x y; funext U; change part T o R U ((P (x+y)).x) + ∑' i,f _ i U= (part T o R U ((P x).x) + ∑' i,f x i U)+(part T o R U ((P y).x)+∑' i,f y i U)
    rw [h.x.map_add,map_add]; simp_rw [(fun i=> (hv i U).map_add x y), (hf x U).tsum_add (hf y U)]; ring
  intro a x; funext U;change part T o R U ((P (a • x)).x) + ∑' i, f _ i U=a • (part T o R U ((P x).x) + ∑' i,f x i U)
  rw [h.x.map_smul,map_smul]; simp_rw [(fun i=> (hv i U).map_smul a x), (hf x U).tsum_const_smul]; exact (smul_add ..).symm
end YM.MergeProof
