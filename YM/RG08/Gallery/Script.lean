import YM.RG08.Gallery.Plates

/-!
# Cofinal Ward extraction: narrow winds evaluated on sparse cover stencils,
 no assertions on zeroth-arity constants beyond cancellation after exact re-expression.
 Works with period chain tending to infinity and eventual collars, not requiring periodic
 heat evaluates cover prescription exactly.
-/
noncomputable section
set_option autoImplicit false
namespace YM.RG08.Gallery
open Forms Glyph Room Camera Finset Lattice Laurent Pert.Bulk Function MvPolynomial Filter Isles
open scoped Topology BigOperators ContDiff PowerSeries Classical
variable {I J : Type}{P:Side}{n:ℕ}

variable {N:ℕ→Side}
lemma moving (hN:Tendsto (fun i=>(N i).val) atTop atTop)(S:Finset (Market I)):∀ᶠ j in atTop, ∀ x∈S,reach (port (N j) x)=x:=by
 rw [eventually_all_finset];intro x hx
 exact (Next.Free.eventually_unfold N hN x.1).mono fun j hj=>by unfold reach port;rw [hj]

/-- Sparse probes with all g-dependence in the body, calibrated logs in same coupling; choose
S as a common finite cover even in transformed stencil. landing uses canonical reach. -/
def native (P:Side)(x:Tray (Market I)): Tray (Cove P I) where
 base:=x.base.image (port P)
 get y := x.get (reach y)
 shut z hz:=x.shut _ (fun h=>hz (by simpa [port,reach] using Finset.mem_image_of_mem (port P) h))
lemma shared (hN:Tendsto (fun i=>(N i).val) atTop atTop)(s t:Tray (Market I)):
  ∀ᶠ j in atTop,
  let X:=s.base∪t.base; Set.InjOn (port (N j)) (X:Set (Market I)) ∧ (∀ x∈X,(native (N j) s).get (port (N j) x)=s.get x ∧ (native (N j) t).get (port (N j) x)=t.get x):=
 (moving hN (s.base∪t.base)).mono fun j hj=>
   ⟨fun x hx y hy h=>by rw [←hj x hx,←hj y hy,h],fun x hx=>⟨congrArg s.get (hj x hx),congrArg t.get (hj x hx)⟩⟩

-- use Tendsto only on each nonconstant stencil slot, constants ignored.
def Grafted (V:∀ j,Script (Cove (N j) I))(F:Script (Market I)):Prop:=∀ e n,0<n→∀ t,Tendsto (fun i=>V i e n (port (N i) ∘ t)) atTop (𝓝 (F e n t))

private lemma priced_volume {k e:ℕ}(ht:Tendsto (fun i=>(N i).val) atTop atTop)(v:Tray (Market I)){V:∀ j,Script (Cove (N j) I)}{F:Script (Market I)}(h:Grafted V F)(he:0<k)(i:ℕ):
 Tendsto (fun j=>tap i (volume (V j e k) (native _ v))) atTop (𝓝 (tap i (volume (F e k) v))):=by
 let S:= v.base
 let s:=desks S k
 have eqd (P:Side): (s.image (fun x:Tape k (Market I)=> (port P ∘ x)))=desks (native P v).base k:=by
    ext x;simp only [s,desks,Fintype.mem_piFinset, Finset.mem_image];constructor
    · rintro ⟨i,hi,rfl⟩ j;exact Finset.mem_image_of_mem _ (hi _)
    intro H
    choose t ht hh using fun j=>Finset.mem_image.mp (H j : x j ∈ _)
    exact ⟨t,ht,funext hh⟩
 have hs :∀ᶠ j:ℕ in atTop,tap i (volume (V j e k) (native _ v))= ∑ x∈s,V j e k (port (N j) ∘ x) * tap i (fret v.get x):=by
    filter_upwards [moving ht S] with j H
    rw [volume,←eqd, Finset.sum_image (by
      intro a ha b hb hab
      funext l
      have he (a:Tape k (Market I))(ha:a∈s):a l=reach (port (N j) (a l)):= (H _ (Fintype.mem_piFinset.mp ha l)).symm
      rw [he a ha,he b hb]; exact congrArg (reach (I:=I)) (congrFun hab l)),tap,map_sum];apply Finset.sum_congr rfl;intro x hx
    have hv : fret (native (N j) v).get (port (N j) ∘ x)=fret v.get x:=by unfold fret;apply Finset.prod_congr rfl;intro a _;change v.get (reach (port (N j) _))=_;rw [H _ (Fintype.mem_piFinset.mp hx a)]
    rw [hv,PowerSeries.coeff_smul,smul_eq_mul]
 rw [volume,tap,map_sum]; simp_rw [PowerSeries.coeff_smul,smul_eq_mul]; refine Tendsto.congr' (hs.mono (fun _ h=> h.symm)) (tendsto_finsetSum _ (fun x _ => (h _ _ he x).mul_const _))

private lemma still_volume (v:Tray I)(f:Flake 0 I) (s:Tray I):volume f s=volume f v:=by
 rw [volume_s _ _ (s.base∪v.base) (Finset.subset_union_left),volume_s _ _ (s.base∪v.base) Finset.subset_union_right];apply Finset.sum_congr rfl; intro j _; rw [fret,fret,Finset.prod_of_isEmpty,Finset.prod_of_isEmpty]

lemma published {V:∀ j,Script (Cove (N j) I)}{F:Script (Market I)}(h:Grafted V F)(ht:Tendsto (fun i=>(N i).val) atTop atTop)(v w:Tray (Market I))(i:ℕ):
   Tendsto (fun j=>tap i (announced (V j) (native _ v) - announced (V j) (native _ w))) atTop (𝓝 (tap i (announced F v-announced F w))) :=by
 simp only [tap,announced,dubbed,map_sub,PowerSeries.coeff_mk,map_sum,←Finset.sum_sub_distrib]
 refine tendsto_finsetSum _ fun a ha=>tendsto_finsetSum _ fun b hb=>?_
 rcases b with _|b
 · simp_rw [still_volume v _ w, still_volume (native _ v) _ (native _ w),sub_self];exact tendsto_const_nhds
 exact (priced_volume ht v h (Nat.zero_lt_succ _) (i-a)).sub (priced_volume ht w h (Nat.zero_lt_succ _) (i-a))

lemma anchor {V:∀ j,Script (Cove (N j) I)}{F:Script (Market I)}(h:Grafted V F)(ht:Tendsto (fun i=>(N i).val) atTop atTop)(v w:Tray (Market I))
    [Fintype I]
    (he:∀ᶠ j:ℕ in atTop,breath (native _ v).get (stock (V j))=breath (native _ w).get (stock (V j))):announced F v=announced F w:=by
 apply sub_eq_zero.mp; ext e :1; change tap _ _=tap _ _
 have hh:=published h ht v w e
 have hy:=he.mono (fun j h=>show tap e (announced (V j) (native _ v) - announced (V j) (native _ w))=tap e (0:Dig) by rw [←cry,←cry,h,sub_self]);exact tendsto_nhds_unique hh (Tendsto.congr' (hy.mono fun _ h=>h.symm) tendsto_const_nhds)
end YM.RG08.Gallery
