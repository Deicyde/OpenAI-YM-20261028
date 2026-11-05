import YM.TraceExtension.Perfect.Pace
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Perfect
open Function Filter Matrix Lattice Precision Laurent Stationary Bloch Exterior Tree RG Wilson Finset Push.Uniform
open scoped BigOperators Topology ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{f:Side}
def topF : Peat G f →ₗ[ℝ] (Acr G f→ℝ) :=
  {toFun:=ballX, map_add':=fun _ _=>rfl,map_smul':=fun _ _=>rfl}
def follic : Gal G f→ₗ[ℝ] (Acr G f→ℝ) :=
  {toFun:=bottom, map_add':=fun _ _=>funext fun i=>add_dotProduct .., map_smul':=fun u x=>funext fun i=>smul_dotProduct u (x (input G f (bite G _ i).1)) _}
variable {I:Type}[Fintype I][DecidableEq I]
lemma cell_fee (A:I→ℕ)(α:ℝ)(V:Rays I→ℝ)(k:ℕ)(q:ℝ)(h:ContDiffAt ℝ ω V 0): cost A α 4 0 (leaf (q • V) 0 k) = |q| * cost A α 4 0 (leaf V 0 k):=by
 unfold cost leaf bank; rw [iteratedFDeriv_const_smul_apply]; swap; · exact h.of_le le_top
 simp only [_root_.smul_apply,norm_smul, Real.norm_eq_abs, mul_left_comm |q|, Finset.mul_sum]
variable {V:Type} {F:Filter V}{n:V→Side} {d k:ℕ}{α D C:ℝ}{x:∀ i,Site (n i)} {fZ g:∀ i,Acr G (n i)→ℝ}
structure Ear (F:Filter V) (x:∀ i, Site (n i))(f:∀ i,Acr G (n i)→ℝ)(α:ℝ)(k:ℕ)(C:ℝ): Prop where
 h(w): ContDiffAt ℝ ω (f w) 0
 fee: earns F (fun w=>cost (landW (x w)) α 4 0 (leaf (f w) 0 k)) C
namespace Ear
lemma plus (hx:Ear F x fZ α k C)(h:Ear F x g α k D): Ear F x (fun w=> fZ w+g w) α k (C+D):=by
 refine ⟨fun w=> (hx.h w).add (h.h w),(hx.fee.add h.fee).tighten (Eventually.of_forall fun i=>?_)⟩
 unfold leaf; rw [iteratedFDeriv_add_apply ((hx.h i).of_le le_top) ((h.h i).of_le le_top)]; exact cost_add ..
lemma grind (p:ℝ)(h:Ear F x fZ α k C): Ear F x (fun w=>p • fZ w) α k (|p| *C):=⟨fun w=>(h.h w).const_smul p, (h.fee.unit (abs_nonneg p)).tighten (Eventually.of_forall fun w=>(cell_fee _ _ _ _ _ (h.h w)).le)⟩
lemma except (hx:Ear F x fZ α k C)(h:Ear F x g α k D): Ear F x (fun w=>fZ w-g w) α k (C+D):=by
 have ht:= hx.plus (h.grind (-1)); simp only[abs_neg,abs_one,one_mul,neg_one_smul,← sub_eq_add_neg] at ht; exact ht
lemma up (hp:Ear F x fZ α k C)(h:C≤D): Ear F x fZ α k D:=⟨hp.h,hp.fee.higher h⟩
lemma empty (hp : 0 ≤ C): Ear F x (fun w=> (0 : Acr G (n w) →ℝ)) α k C:=by refine ⟨fun w=> contDiffAt_const,earns.eventually (Eventually.of_forall fun i=>?_)⟩; simp [cost,leaf,bank,hp]
lemma likewise (hp:Ear F x fZ α k C)(h:∀ w,fZ w=ᶠ[𝓝 0] g w): Ear F x g α k C:=by refine ⟨fun w=>(hp.h w).congr_of_eventuallyEq (h w).symm,hp.fee.tighten (Eventually.of_forall (fun w=>?_))⟩; unfold leaf; rw[(h w|>.iteratedFDeriv ℝ k).eq_of_nhds]
end Ear
structure Tip (F:Filter V) (x:∀ i, Site (n i))(f:∀ i,Acr G (n i)→ℝ)(P:Tit G→Tit G→ℝ)(d:ℕ):Prop where
 h(w): ContDiffAt ℝ ω (f w) 0
 sees: Stoke F x f P d
namespace Tip
variable {P Q:Tit G→Tit G→ℝ}
lemma plus (hx:Tip F x fZ P d)(h:Tip F x g Q d): Tip F x (fun w=> fZ w+g w) (P+Q) d:=by
 refine ⟨fun w=> (hx.h w).add (h.h w),⟨fun i j hi=> ((hx.sees.taste i j hi).add (h.sees.taste i j hi)).congr fun w=> ?_⟩⟩; rw [iteratedFDeriv_add_apply ((hx.h w).of_le le_top) ((h.h w).of_le le_top)]; rfl
lemma grind (p:ℝ)(h:Tip F x fZ P d): Tip F x (fun w=>p • fZ w) (p • P) d:=by
 refine ⟨fun w=>(h.h w).const_smul p, ⟨fun i j hp=> ((h.sees.taste i j hp).const_mul p).congr fun w=>?_⟩⟩
 rw [iteratedFDeriv_const_smul_apply]; rfl; exact (h.h w).of_le le_top
lemma except (hx:Tip F x fZ P d)(h:Tip F x g Q d): Tip F x (fun w=>fZ w-g w) (P-Q) d:=by
 have ht:= hx.plus (h.grind (-1)); simp only[neg_one_smul,← sub_eq_add_neg] at ht; exact ht
lemma empty (F:Filter V)(x:∀ i, Site (n i)) (d): Tip F x (fun w=>(0:Acr G (n w) →ℝ)) 0 d:=by refine ⟨fun _=>contDiffAt_const,⟨fun i j _=> tendsto_const_nhds.congr fun w=>?_⟩⟩; simp
lemma likewise (hp:Tip F x fZ P d)(h:∀ w,fZ w=ᶠ[𝓝 0] g w): Tip F x g P d:= by
 refine ⟨fun w=>(hp.h w).congr_of_eventuallyEq (h w).symm,⟨fun i j hi=>(hp.sees.taste i j hi).congr (fun w=>?_)⟩⟩; rw[(h w|>.iteratedFDeriv ℝ 2).eq_of_nhds]
end Tip
lemma Sheaf.ear (X: Sheaf)(x:∀ w:V,Site (n w))(f:∀ w:V,Cover→Acr G (n w)→ℝ)(a:Cover)(p:ℕ)(H:∀ b:Cover,Laurent.size b ≤ Laurent.size a+p+X.radius→ Ear F x (fun w=> f w b) α k C):
   Ear F x (fun w=>Sheaf.take (f w) X a) α k (X.debt*C):=by
 induction X generalizing p f C a with
 | stay=>rw [Sheaf.debt];simp only[Sheaf.take,zero_mul]; exact Ear.empty le_rfl
 | mon z=> simpa only [Sheaf.take,Sheaf.debt,one_mul] using H _ ((size_add ..).trans (Nat.add_le_add_right (Nat.le_add_right (size a) p) (size z)))
 | duo X Y v h=> rw[debt,add_mul]; simp only[take,Pi.add_apply]; exact (v f a p (fun w hp=> H w (le_trans hp (by simp only[radius];omega)))).plus (h f a p (fun w hp=> H w (le_trans hp (by simp only[radius];omega))))
 | scale c X ih=> rw[debt,mul_assoc]; simp only[take,Pi.smul_apply]; exact (ih f a p H).grind c
 | mix X Y v h=> rw[debt,mul_assoc]; simp only[take]; refine v _ a p (fun w hp=> h f w 0 (fun i ht=> H i ?_)); unfold radius; omega
lemma Sheaf.top (X:Sheaf)(x:∀ w:V,Site (n w))(P:Tit G→Tit G→ℝ)(f:∀ w:V,Cover→Acr G (n w)→ℝ)(a:Cover)(H:∀ b:Cover, Tip F x (fun w=>f w b) P d): Tip F x (fun w=>Sheaf.take (f w) X a) (X.gold • P) d:=by
 induction X generalizing P a f with
 | stay=> simp only[take,gold,zero_smul]; exact Tip.empty ..
 | mon v=>simpa only[take,gold,one_smul] using H (a+v)
 | duo V W p h=>simp only[take,gold,add_smul]; exact (p P f a H).plus (h P f a H)
 | scale c V h=>simp only[take,gold,mul_smul]; exact (h P f a H).grind c
 | mix V W p h=>simp only[take,gold,mul_smul]; exact p _ _ _ (fun b=> h _ _ _ H)
end YM.Trace.Perfect
