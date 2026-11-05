import YM.RG08.Quarry.Quires

/-! # Signed vacuum law on sparse inputs including inflight frame. -/
noncomputable section
set_option autoImplicit false
namespace YM.RG08.Quarry
open Filter Function Matrix MeasureTheory Finset Lattice Exterior Wilson RG Precision Stationary Work.F05 Tree Carrel Prism Tack Camera Slate Gallery
open Forms Rudder Anchor Isles Laurent Pert.Bulk Mount Glyph Room Bloch
open scoped Classical Matrix ContDiff Topology BigOperators InnerProductSpace PowerSeries ENNReal Matrix.Norms.Frobenius
variable {c :Side}{G:Gauge}(s:Signed)
variable {I : Type}
def spin (v:Tray (Mix I 1)):Tray (Mix I 1) where
 base:=v.base.image (atlas s⁻¹)
 get i:= supply s i.2 • v.get (atlas s i)
 shut i hi:=by rw [v.shut _ (fun ht=>hi (by refine Finset.mem_image.mpr ⟨atlas s i,ht,(lodge s).left_inv i⟩)),smul_zero]
lemma spin_reach (x:Tray (Mix I 1)):
 ∀ᶠ n in atTop,∀ i:Cmix (Isles.chain n) I 1, (Gallery.native _ (spin s x)).get i=supply s i.2 • (Gallery.native _ x).get (Carrel.badge s i):=by
 filter_upwards [moving Isles.rise x.base,moving Isles.rise (spin s x).base] with n hx ht
 intro i;change supply s i.2 • x.get _=supply s i.2 • x.get (reach _)
 apply congrArg
 let y : Mix I 1:=atlas s (reach i)
 let z:=reach (Carrel.badge s i);let k:=Isles.chain n
 have hh:port k y=port k z:=by simp [y,z,←badge_atlas]
 by_cases h:y∈x.base
 · have he:=hx _ h
   exact congrArg _ (he.symm.trans ((congrArg Isles.reach hh).trans (by simp [z]))) -- he : reach port y; after hh reach port z=z defeq? z=reach badge; reaches, not defeq

 by_cases hB:z∈x.base
 · have hv :atlas s⁻¹ z∈ (spin s x).base:=Finset.mem_image_of_mem _ hB
   have hD : atlas s⁻¹ z= reach i:=by
      rw [←ht _ hv,← badge_atlas,show port k z=Carrel.badge s i from reaches _,badge_com,inv_mul_cancel,badge_id]
   have hw:y=z:= by unfold y; rw [←hD];exact (lodge s).right_inv z -- hD rewrite in goal? equality in LHS starts reach i vs iz; need ←
   exact congrArg _ hw
 exact (x.shut _ h).trans ((x.shut _ hB).symm)

lemma salt (v:ℝ){I:Type}[Fintype I](p:Still I)(he:Pace p):eye (v • p)=v • eye p:=by
 ext k :1;change tap _ _=tap _ _;rw [eye, look,flask_scale he];change PowerSeries.coeff _ _=PowerSeries.coeff _ _;rw [PowerSeries.coeff_smul,PowerSeries.coeff_smul];exact congrArg (v • ·) ((look (flask p) k).symm)

variable {P:Patch}{K:KernelChoices}(h:P.Branches K G)(A B:Bed)(C:Castle G)(Z:ChartRatio G)
def SignedLaw (V:Gallery.Script (Market (Loc G 1))): Prop:=∀ (s:Signed)(x:Tray (Market (Loc G 1))),announced V x=announced V (spin s x)
lemma haven {I:Type}[Fintype I](f:I→Dig)(z:ℝ)(i:I):breath f (eye (fun x:Cellar I=>z*x i))=z • (f i):=by
 rw [show (fun x:Cellar I=>z*x i)=z • fun x=>x i from rfl,salt _ _ (contDiff_apply ℝ ℝ _).contDiffAt,eye_reader,_root_.map_smul,bases_x]

lemma spectacles (F:Foyer P K A B C Z): SignedLaw (vault G P K h C Z A B):=by
 intro s x
 apply deliver P K h A B C Z (X:=fun c=>Lines G c 1) (Y:=fun c=>Lines G c 1) F (fun _=>id) (fun _=>id)
 filter_upwards [spin_reach s x] with n hx
 let c:=Isles.chain n;let S:= Line.habitat P K c;let T:=Line.green S
 let f:Heights S T G (Lines G c 1)→Dig:=Sum.elim (fun _=>0) (Gallery.native _ x).get
 refine ⟨certify S T A B _ _ _ _ (warp S T s) Z F.eye,f,?_,fun _=>rfl⟩
 intro q
 change breath f (eye (fun z=>blade s (z ∘ Sum.inr) q))=(Gallery.native c (spin s x)).get q
 exact (haven f (supply s q.2) (Sum.inr (Carrel.badge s q))).trans ((hx q).symm)
lemma sunglasses (V:Gallery.Script (Market (Loc G 1)))(h: SignedLaw V)(e:ℕ):Rotation V e:=by
 intro a s p
 let v:=pend p a
 refine ⟨v,spin s v,funext fun i=>by simp [Demo.flat,v,pend,Demo.pump,Demo.reals],funext (fun i=> ?_),congrArg _ (h s v)⟩
 simp only [Demo.flat,spin,v,pend,Demo.pump,Demo.reals,rot, Pi.smul_apply,smul_eq_mul]; -- cc scalar
 rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_smul];simp;ring
end YM.RG08.Quarry
