import YM.TraceExtension.Perfect.Theatre

/-! # Compactness on origin decks, including perturb entries with one stopped chute -/
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Perfect
open Function Filter Matrix Lattice Precision Laurent Stationary Bloch Exterior Tree RG Wilson
open scoped BigOperators Topology ContDiff Matrix.Norms.Frobenius
variable {c f:Side}{G:Gauge}{P P':Patch}{Y:KernelChoices}
def spaceFee (P : Patch):ℕ:= Finset.univ.sup (fun i: Plaza P=> size i.val)
lemma space_check (v:Plaza P)(o:Site f): separation o (wrap f v.val+o) ≤ spaceFee P:=by
 rw [separation_comm,separation,add_sub_cancel_right]; exact (Next.Free.within_size ..).trans (Finset.le_sup (s:=Finset.univ) (f:=fun i:Plaza P=>size i.val) (Finset.mem_univ v))

-- tags cast helpers
def invite (h:P=P'):BassInput G P ≃L[ℝ] BassInput G P':=h ▸ ContinuousLinearEquiv.refl ℝ (BassInput G P)
lemma host_l (h:P=P')(x:BassInput G P)(t:Bool)(z: Plaza P')(m): invite h x (.inl (t,z,m))=x (.inl (t,h.symm ▸ z,m)):=by subst P';rfl
lemma host_r (h:P=P')(x:BassInput G P)(i): invite h x (.inr i)=x (.inr i):=by subst P'; rfl
lemma tuneMove (h:P=P') (x y:BassInput G P) (i j): fderiv ℝ (tuneP i j) (invite h x) (invite h y)=fderiv ℝ (tuneP i j) x y:=by subst P'; rfl
lemma pillowMove (h:P=P') (x:BassInput G P)(i j): pillow i (invite h x) j=pillow i x j:=by subst P';rfl
variable {S: StepData c f}
lemma bass_tag (i : Site c)(p : Lines G f 1)(x:Piano G S.patch): |pianist S i (outTest (desk (I:=Lines G f 1) p)) x|≤1:=by
 rcases x with ⟨t,a,l⟩|(⟨b,k,d⟩|⟨b,d⟩)
 · cases t
   · change |(0:ℝ)| ≤ _; simp
   change |desk p (wrap f a.val +S.ratio.embed i,l)| ≤ _; by_cases h: (wrap f a.val+S.ratio.embed i,l)=p <;> simp [desk,Pi.single_apply,h, Ne.symm]
 · cases b<;> (change |(0:ℝ)|≤_;simp)
 cases b<;> (change |(0:ℝ)|≤_;simp)
lemma bass_far (i:Site c)(p: Lines G f 1)(h:spaceFee S.patch < separation (S.ratio.embed i) p.1): pianist S i (outTest (desk p))=0:=by
 ext1 x; rcases x with ⟨t,a,b⟩|(⟨d,m,b⟩|⟨d,b⟩)
 · cases t; · rfl
   change desk (I:=Lines G f 1) p (wrap f a.val+S.ratio.embed i,b)=0; apply Pi.single_eq_of_ne
   intro hx; apply h.not_ge; rw [← show _=p from hx]; exact space_check a _
 · cases d<;> rfl
 cases d<;> rfl

-- price root op fix derivative, using ° path. holds on ALL nearest patch reps.
lemma fix_meter (S:StepData c f)(b:Site c)(i:Body 1 f) :
   |fixRoot S (b,vac) i|≤16*S.patch.radius ∧ (12*S.patch.radius<separation (S.ratio.embed b) i.1 → fixRoot S (b,vac) i=0):=by
 let v : form 1 f:=Pi.single i 1
 let V:= fixRoot S
 have he : fixRoot S (b,vac) i=(V*ᵥ v) (b,vac):=by unfold v;rw [Matrix.mulVec_single_one];rfl
 have hx x z (h:0≤(z:ℝ))(hp:∀ j:Body 1 f,separation x j.1≤ 12*S.patch.radius→|v j|≤z)(hh:x=S.ratio.embed b): |fixRoot S (b,vac) i|≤16*S.patch.radius*z:=by
      subst x; rw [he]; exact Progress.StationaryScenes.Response.psi S v _ b _ z h hp (by rw [separation_self]; omega)
 constructor
 · simpa only [mul_one] using hx _ 1 zero_le_one (fun j _=>by by_cases h:j=i <;> simp [v,h]) rfl
 intro h; have ht:= hx (S.ratio.embed b) 0 le_rfl (fun j hx => by have hh : j≠i := fun H=> h.not_ge (H ▸ hx); simp [v,hh]) rfl
 rw [mul_zero] at ht; simpa using! ht

-- the entire columns shuttle vanish as germs outside finite radius.
def railMax (P:Patch):= max (spaceFee P) (12*P.radius+P.L.val)
lemma candry (e:Lines G f 1)(j:Site c)(x:Stationary.Joint G c f) :
   let d: G.Color:= edgeColor (desk e) (edgeOf (e.1,e.2.1)); let R:=(e.1,e.2.1); gaugeColor (armament S x (desk e)) j = fixRoot S (j,vac) R • G.adjoint (road S x j e.1) d:=by
 intro d R; rw [armament_point]; apply Eq.trans (Finset.sum_eq_single R ?_ ?_)
 · rfl
 · intro i _ hp; have he : edgeColor (desk e) (edgeOf i)=0:=by
       ext k; rw [edge_parts]; apply Pi.single_eq_of_ne;intro h; exact hp (congr_arg (fun j: Lines G f 1=> ((j.1,j.2.1):Body 1 f)) h)
   rw [he,map_zero,smul_zero]
 simp
lemma cant_dry (j : Lines G c 1)(x: Stationary.Joint G c f)(V:Config G c)(e:Lines G f 1)(he: railMax S.patch<separation (S.ratio.embed j.1) e.1): cant V (armament S x (desk e)) j=0:=by
 let u:Body 1 c:=(j.1,j.2.1); let b:=edgeOf u; change cant V (armament S x (desk e)) (u.1,u.2,j.2.2)=0
 rw [← edge_parts (cant V (armament S x (desk e))) u j.2.2]; rw [cant_at]; simp_rw [candry]
 have hp : 12*S.patch.radius<separation (S.ratio.embed j.1) e.1:= lt_of_le_of_lt ((Nat.le_add_right ..).trans (le_max_right ..)) he
 have ht : 12*S.patch.radius< separation (S.ratio.embed (b.1+step b.2)) e.1:=by
      have ht:=separation_triangle (S.ratio.embed j.1) (S.ratio.embed (b.1+step b.2)) e.1
      have hz: separation (S.ratio.embed j.1) (S.ratio.embed (b.1+step b.2))≤S.patch.L.val:=by
          have hf:= Next.Free.scaled_root S.ratio j.1 (b.1+step b.2); refine hf.trans (by change S.patch.L.val * separation j.1 (j.1+step b.2) ≤ _; refine le_trans (Nat.mul_le_mul_left _ (show separation j.1 (j.1+step b.2) ≤ 1 from ?_)) (le_of_eq (Nat.mul_one _)); rw [separation_comm,separation,add_comm j.1,add_sub_cancel_right]; exact pdist_step _)
      unfold railMax at he; omega
 change (((fixRoot S (j.1,vac) (e.1,e.2.1)) • _-G.adjoint _ ((fixRoot S (b.1+step b.2,vac) (e.1,e.2.1)) • _)):G.Color) j.2.2=0
 rw [(fix_meter ..).2 hp, (fix_meter ..).2 ht];simp
lemma rail_far {X:Type}[NormedAddCommGroup X][NormedSpace ℝ X][FiniteDimensional ℝ X]{t:S.Choices}{p : Clip}{Y: X → Stationary.Joint G c f}{R:PathData G}{α M C:ℝ}(V:X→Config G c)
  (hR:S.patch.Branches S.kernel G)(hz:R.Bounds p α M C)(hU:Thaw Y 0)(w:Y 0=1)(A:Lines G f 1)(i:Lines G c 1)(h: railMax S.patch<separation (S.ratio.embed i.1) A.1):
    (fun x=> shuttle S t (Y x) (V x) (desk A) i)=ᶠ[𝓝 0] 0 :=by
 rcases i with ⟨v,k,j⟩; obtain ⟨k,rfl⟩:=axisEquiv.surjective k
 filter_upwards [tunes_the S t hR hz hU w (desk A) v k j] with x hx
 rw [bass_far v A ((le_max_left ..).trans_lt h),map_zero] at hx
 unfold shuttle; rw [_root_.add_apply,Pi.add_apply,ContinuousLinearMap.comp_apply,show axisEquiv k=coord k from rfl,hx,zero_add,cant_dry (v,coord k,j) (Y x) (V x) A h];rfl
end YM.Trace.Perfect
