import YM.TraceExtension.Perfect.Pallas
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Perfect
open Function Filter Matrix Lattice Precision Laurent Stationary Bloch Exterior Tree RG Wilson Finset
open scoped BigOperators Topology ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{n:Side}{α :ℝ}
def ride (x:Site n) : Config G n→ Config G n:= Lattice.translate x
def paceV (x:Site n) : Site n≃ Site n:=Equiv.addRight x
variable {I:Type}[Fintype I]
def rideI (x:Site n) : Site n×I≃ Site n×I := Equiv.prodCongr (paceV x) (Equiv.refl _)
def rideC (x:Site n): Link G n →L[ℝ] Link G n:= ContinuousLinearMap.pi (fun i=> ContinuousLinearMap.proj (rideI x i))
def rideA (x:Site n) : Acr G n→L[ℝ] Acr G n := ContinuousLinearMap.pi fun i=> ContinuousLinearMap.proj (Equiv.sumCongr (rideI x) (rideI x) i)
abbrev ry (x:Site n) : Gal G n→ₗ[ℝ] Gal G n := {
 toFun:= fun g U=> rideC (-x) (g (ride x U))
 map_add':=fun f g=> funext fun x=> map_add ..
 map_smul':=fun t v=> funext fun U=> (rideC (-x)).map_smul t (v (ride x U)) }
abbrev rj (x:Site n): Peat G n→ₗ[ℝ] Peat G n := {
 toFun:=fun f U=> f (ride x U)
 map_add':=fun _ _=> rfl
 map_smul':=fun _ _=>rfl }
lemma pace_at (x y: Site n)(U:Config G n)(i): ride y U (x,i)=U (x+y,i):=rfl
lemma pace_add (x y : Site n)(U:Config G n): ride x (ride y U)=ride (x+y) U:=by funext i; rcases i with ⟨i,k⟩; rw [pace_at,pace_at,pace_at,add_assoc]
lemma spin_at (u:Link G n)(x y:Site n)(i): edgeColor (rideC y u) (x,i)=edgeColor u (x+y,i):= rfl
lemma rideC_sum (x y: Site n)(U:Link G n): rideC x (rideC y U)= rideC (x+y) U:=by ext1 i; change U (i.1+x+y,i.2)=U (i.1+(x+y),i.2); rw [add_assoc]
lemma rideC_neg (x:Site n)(U:Link G n): rideC (-x) (rideC x U)=U:=by rw [rideC_sum,neg_add_cancel]; ext1 i; change U (i.1+0,_)=_; rw [add_zero]; rfl
lemma r_imp (U: Link G n)(x:Site n): input G n (rideC x U)=ride x (input G n U):=by funext i; rcases i with ⟨i,j⟩; rw [pace_at,input_color,input_color,spin_at]
lemma take_px (x : Site n)(a : Peat G n): (rj x a) ∘ input G n= (a ∘ input G n) ∘ rideC x:=funext fun i=> congr_arg a (r_imp i x).symm
lemma dot_bend (U V:Link G n)(i:Site n): (rideC i U) ⬝ᵥ rideC i V= U ⬝ᵥ V := by
 unfold dotProduct; exact Equiv.sum_comp (rideI i) (fun j:Lines G n 1=> U j*V j)
lemma ride_bottom (x : Site n)(a:Gal G n): bottom (ry x a)= bottom a ∘ rideA x :=by
 funext z; let U:=a (ride x (input G n (bite G n z).1)); let X:=rideA (G:=G) x; let V:=(bite G n z).2
 unfold bottom; simp only[Function.comp_apply]; rw [show (bite G n (X z)).1= rideC x (bite G n z).1 from rfl,r_imp]; change rideC (-x) U ⬝ᵥ V= U ⬝ᵥ rideC x V
 rw [← rideC_neg x V]; nth_rw 1 [dot_bend]; rw [rideC_neg]
lemma ride_ball (x:Site n)(a:Peat G n): ballX (rj x a)=ballX a ∘ rideA x:=funext fun z=> congr_arg a (r_imp (bite G _ z).1 x).symm
lemma taking_loom (x: Site n)(a:Peat G n)(h:a∈loom G n): (rj x a)∈ loom G n:=by
 obtain ⟨h,p⟩:=h; change Cleric a at h; change braid _ _ _ _ at p
 have hv:Army (fun i:Link G n=> input G n i) 0:= Army.powL contDiffAt_id
 let F:= rj x a
 have hs: ContDiffAt ℝ ω (F ∘ input G n) 0:= (take_px x a).symm ▸ ContDiffAt.comp _ ((map_zero (rideC x)).symm ▸ h.dye) (rideC x |>.contDiff.contDiffAt)
 refine ⟨⟨hs, fun T _ _ _ _ V k u hV hp ht h'=>?_⟩,?_⟩
 · let g (i:T):= ride x (V i); let p(i:T):= fun v:Site n=>k i (v+x)
   have hx: (fun i=> (rj x a) (Lattice.gauge (k i) (V i)))=(fun i=> a (Lattice.gauge (p i) (g i))):=by funext i; change a (ride _ _)=_; congr 1; unfold ride Lattice.translate Lattice.gauge g p; ext1 j; simp only [ride,Lattice.translate]; rw [add_right_comm j.1]
   rw[hx]; refine h.jacket T g p u (fun i=> hV (rideI x i)) (show g 0=1 from by unfold g; rw [hp];rfl) (fun i=>ht (i+x)) (funext fun _=>congr_fun h' _)
 change braid _ _ _ _; rw[take_px]; exact wove (w:=rideC x) ((map_zero (rideC x)).symm ▸ p) ((map_zero (rideC x)).symm ▸ h.dye) contDiffAt_const ((rideC x).contDiff.contDiffAt)
lemma taking_rain (x:Site n)(a:Gal G n)(h:a∈rains G n): (ry x a)∈rains G n:=by
 obtain ⟨h,p⟩:= h; change Cloaked a at h; change a 1=0 at p
 have ht: ry x a ∘ input G n=rideC (-x) ∘ ((a ∘ input G n) ∘ rideC x):=funext fun i=> congr_arg (rideC (-x)) (congr_arg a (r_imp i x).symm)
 refine ⟨⟨ht.symm ▸ ContDiffAt.comp _ (rideC (-x) |>.contDiff.contDiffAt) (ContDiffAt.comp _ ((map_zero (rideC x)).symm ▸ h.dye) (rideC x|>.contDiff.contDiffAt)),fun T _ _ _ _ V k u hV hu hk ph=>?_⟩,by change rideC (-x) (a (ride x 1))=0; rw [show ride x (1:Config G n)=1 from rfl,p,map_zero]⟩
 let g(i:T):=ride x (V i); let p(i:T):=fun v:Site n=>k i (v+x)
 filter_upwards [h.jacket T g p u (fun i=>hV (rideI x i)) (show g 0=1 from by unfold g;rw [hu];rfl) (fun i=>hk (i+x)) (funext fun _=>congr_fun ph _)] with i hv
 change rideC (-x) (a (ride x (Lattice.gauge (k i) (V i))))=armor (k i) (rideC (-x) (a (g i)))
 have he: ride x (Lattice.gauge (k i) (V i))=Lattice.gauge (p i) (g i):=by ext1 j; unfold ride g p Lattice.translate Lattice.gauge; simp only[ride,Lattice.translate, Lattice.gauge]; rw [add_right_comm j.1]
 rw [he, hv]; apply edgeColor.injective; funext j; rcases j with ⟨j,l⟩; rw [spin_at,armor_at,armor_at,spin_at]; unfold p; rw [neg_add_cancel_right]

lemma ride_jet (v:ℝ)(a:Acr G n→ℝ)(x:Site n)(o:Site n)(h:ContDiffAt ℝ ω a 0)(k:ℕ):
    cost (landW (o+x)) v 4 0 (leaf (a ∘ rideA x) 0 k)=cost (landW o) v 4 0 (leaf a 0 k):=by
 let p: pairA G n ≃ pairA G n:= Equiv.sumCongr (rideI x) (rideI x)
 let q:= (Equiv.arrowCongr (Equiv.refl (Fin k)) p)
 have he(i:pairA G n): landW (o+x) (p i)=landW o i:=by cases i with
   | inl i=> change separation (o+x) (i.1+x)=_; simp only [separation,add_sub_add_right_eq_sub];rfl
   | inr i=> change separation (o+x) (i.1+x)=_; simp only [separation,add_sub_add_right_eq_sub];rfl
 have hz (i:pairA G n): rideA x (desk (p i))=desk i:=by ext j; change desk _ (p j)=desk i j; simp only [desk,Pi.single_apply,p.apply_eq_iff_eq]; split_ifs <;> rfl
 unfold cost; nth_rw 1 [← Equiv.sum_comp q]; apply sum_congr rfl; intro i _; unfold leaf bank; rw[show limitN (landW (o+x)) (q i)=limitN (landW o) i from ?_,wired (rideA x) (by rw [map_zero];exact h.analyticAt),map_zero]; rotate_left
 · unfold limitN; congr 1; exact funext fun j=> he (i j)
 congr 3; funext j; exact hz _
lemma spin_ball (s:Tit G)(x o:Site n): rideA x (ballad s (o+x))=ballad s o:=by
 ext1 i; let p:=Equiv.sumCongr (rideI (I:=Loc G 1) x) (rideI (I:=Loc G 1) x)
 change ballad s _ (p i)= _
 unfold ballad; have ht(i:Lines G n 1) : strollT s (o+x) (rideI x i)=strollT s o i:=by unfold strollT; change (if i.2=_ then s.1.price (lift (i.1+x-(o+x))) else 0)=_; rw [add_sub_add_right_eq_sub]
 split<;> cases i <;> first|exact ht _|rfl
lemma ride_tell {o:Site n}{v:Acr G n→ℝ}{Q d ε}(a:Site n)(h:Testify o v Q d ε)(he:ContDiffAt ℝ ω v 0): Testify (o+a) (v ∘ rideA a) Q d ε:=by
 refine ⟨fun i j hv=>?_⟩; rw [wired (rideA a) (by rw [map_zero]; exact he.analyticAt),map_zero]; convert h.bill i j hv using 4; funext k; fin_cases k <;> first| exact spin_ball i a o| exact spin_ball j a o
end YM.Trace.Perfect
