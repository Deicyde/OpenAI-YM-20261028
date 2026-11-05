import YM.RG08.Invert.Limb
/-! # Anchor inversion for tree adjustment \phi, no orientation claim
 for unused codes at root; paid site-Series too. Need genuine cover norm. -/
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
noncomputable section
namespace YM.RG08.Invert
open Function Filter Lattice Wilson Exterior Precision Laurent Next.Free Next.Free.Flight RG RG.Supply Bloch Input Matrix
open Planned.PrimaryIntegral295 Carrier
open Stationary Analysis FreeResolvent Tree UVExt.Paths Reflect
open scoped BigOperators Topology Real Classical Matrix ContDiff
variable {G:Gauge}{i j k t r:ℕ}{L c f:Side}{S:StepData c f}
section extension
variable {m:ℕ→Side} {α β:Type}
variable {A:Cross L α β}
private lemma nomF (B:Ratio c f)(P: Cross B.count α β)(x y:Cover)(a:α)(b:β): installed B P (wrap f x,a) (wrap c y,b)= P.acts c (0, wrap B.count x,a) (wrap c (y-cellar B.count x),b) := by
    rw [installed,submatrix_apply,split_co]; dsimp only; rw [Streets.residue,Streets.owner]
    unfold Row.acts; simp only [of_apply,id_eq,map_sub,zero_add]; apply tsum_congr; intro i; simp [sub_eq_iff_eq_add,add_comm]
lemma foyer (h:Whole A)(hp:Tendsto (fun i=>(m i).val) atTop atTop)(x y:Cover)(a b):
    Tendsto (fun i=>installed (⟨L,rfl⟩:Ratio (m i) (m i*L)) A (wrap (m i*L) x,a) (wrap (m i) y,b)) atTop (𝓝 (localeV A x a b y)):= by simp_rw [nomF]; exact entry_limit m hp A h.safe _ _ _
-- explicit at wrap-test (separate to avoid over Step contexts)
private lemma tunnel (g:Ratio c f)(W: Cross g.count α β)(x y:Cover)(a b): installed g W (wrap f x,a) (wrap c y,b)=∑' i, if wrap c y= wrap c i then localeV W x a b i else 0:=by
    rw [nomF]; unfold Row.acts; simp only [Matrix.of_apply,zero_add]
    let z:=cellar g.count x
    rw [← (Equiv.addRight z).tsum_eq (fun i:Cover=>if (wrap c y)=wrap c i then localeV W x a b i else 0)]; apply tsum_congr; intro k
    rw [show Equiv.addRight z k=k+z from rfl,map_add,map_sub]; unfold localeV; rw [show k+z-cellar g.count x=k from add_sub_cancel_right ..]; simp [z,sub_eq_iff_eq_add]
end extension
@[simp] lemma mate_zero (x:Site L): mate L 0 (x,vac)=(-x,vac):= by unfold mate brim; simp [vac]
-- $AntiFull$ oriented sign cost
section covariance
variable {κ:KernelChoices}
lemma gradient_site (Q:Matrix (FreeResolvent.Slot G f 0) (FreeResolvent.Slot G c 1) ℝ)(z:Site f)(a:Axis)(i:G.ColorIndex)(v:FreeResolvent.Slot G c 1):
   (patron G (d 0 f)*Q) (z,coord a,i) v = Q (z+step a,vac,i) v-Q (z,vac,i) v := by
    let x (j):= Q j v
    rw [tensor_same]; change component (tensor G (d 0 f)*ᵥ x) i (z,coord a)=_; rw [component_mul,d_sites]; rfl
private lemma acc {Q:Matrix (FreeResolvent.Slot G f 0) (FreeResolvent.Slot G c 1) ℝ} (h:HeatV (toneP G f 1) (toneP G c 1) (patron G (d 0 f)*Q)) (y y':Cover) (z: G.ColorIndex)(v: FreeResolvent.Slot G c 1) :
    let l x:= Q (wrap f x,vac,z) v+Q (-wrap f x,vac,z) (toneP G c 1 v)
    l y=l y':=by
    intro l; have hh (x:Cover)(a:Axis): l (x+step a)=l x:= by
       have hx:= h.yes (wrap f x,coord a,z) v
       rw [show toneP G f 1 (_,_)= ix (mate f 1 (wrap f x,coord a)) z from rfl, mate_one] at hx
       unfold ix at hx; simp only [gradient_site, sub_add_cancel] at hx
       unfold l; rw [map_add, wrap_step, show -(wrap f x+step a)=-wrap f x-step a by abel]; linarith only [hx]
    have he (w:Lattice.Walk)(x:Cover): l x=l (stop x w):= by
       induction w generalizing x with
       | nil=> rfl
       | cons i w ih=>
         rcases i with ⟨i,u|u⟩ <;> rw [stop,← ih]
         · exact (hh x i).symm
         change l x= l (x+ -step i); rw [← sub_eq_add_neg]; apply Eq.trans _ (hh (x-step i) i); exact congr_arg l (sub_add_cancel ..).symm
    exact (he (route y y' 1) y).trans (congr_arg l (route_end ..))
variable {T:Cross L (Loc G 0) (Loc G 1)}
private lemma compensates (h: Whole T)(hp:∀ c: Side, let f:=c*L; let g:= (⟨L,rfl⟩:Ratio c f); HeatV (toneP G f 1) (toneP G c 1) (patron G (d 0 f)*installed g T)) (x y:Cover) (a:Axis)(i j:G.ColorIndex):
    let s (x y):= localeV T x (vac,i) (coord a,j) y
    s x y = -s (-x) (pole (coord a) y):= by
    intro s; let r:=pole (coord a) y; let u x:= s x y+s (-x) r
    have hx (x x'): u x=u x':= by
       let m(i:ℕ):Side:= (⟨i+1,Nat.succ_pos _⟩:Side); have hv: Tendsto (fun i=>(m i).val) atTop atTop:= tendsto_atTop_mono (fun i => show i ≤ i+1 by omega) tendsto_id
       let g i : Ratio (m i) (m i * L):= ⟨L,rfl⟩; let f i:=m i * L
       let V x y i':= installed (g i') T (wrap (f i') x,vac,i) (wrap (m i') y,coord a,j)
       have hm x : Tendsto (fun i=> V x y i + V (-x) r i) atTop (𝓝 (u x)):= (foyer h hv ..).add (foyer h hv ..)
       refine tendsto_nhds_unique_of_eventuallyEq (hm x) (hm x') (Eventually.of_forall fun k=>?_)
       have hz: ix (wrap (m k) r,coord a) j=toneP G (m k) 1 (ix (wrap (m k) y,coord a) j):= by rw [tone_on]; apply congr_arg (fun x:Co (m k) (TypeFace 1)=> ix x j); exact (cover_mate ..).symm
       change V x y k + V (-x) r k = V x' y k+ V (-x') r k; unfold V; rw [map_neg,map_neg, show (wrap (m k) r,coord a,j) = _ from hz]; exact acc (Q:=installed (g k) T) (hp _) x x' _ _
    have hJ (u:Cover): wrap L (L.val • u)=0:= by rw [map_nsmul]; ext; simp [nsmul_eq_mul,Per]
    have hB (u:Cover):cellar L (L.val • u)=u:= by
       have h:=balance L (L.val • u); rw [hJ,origin_lift,zero_add] at h; exact smul_right_injective _ L.property.ne' h.symm -- k nsmul?
    have hy(y:Cover):Summable (fun u:Cover=> s (L.val • u) y):= by
       let f:=T (0,vac,i) (coord a,j)
       unfold s localeV; simp_rw [hJ,hB]
       let E:Equiv.Perm Cover:= Equiv.subLeft y; exact E.summable_iff.mpr ((h.safe ..).of_norm)
    have hw: Summable (fun i: Cover=>u x):= ((hy y).add ((Equiv.neg Cover).summable_iff.mpr (hy r))).congr (fun i=> ?_)
    · exact eq_neg_of_add_eq_zero_left ((summable_const_iff (β:=Cover) (u x)).mp hw)
    apply Eq.trans _ (hx (L.val• i) x); change s (L.val • i) _ + s (L.val • -i) _=s (L.val • i) _+ s (-(L.val • i)) _; simp only [smul_neg]
lemma AntiTw (h:Whole T) (hp:∀ c:Side, let f:=c*L; let g:= (⟨L,rfl⟩:Ratio c f); HeatV (toneP G f 1) (toneP G c 1) (patron G (d 0 f)*installed g T)) (X:Ratio c f)(hx:X.count=L) :
   let Z:= (hx.symm ▸ T : Cross X.count (Loc G 0) (Loc G 1))
   let A:= installed X Z
   ∀ i j,A i j= - A (toneP G f 0 i) (toneP G c 1 j):= by
    subst L; intro Z A i j; change installed X T i j= -(installed X T (toneP G f 0 i) (toneP G c 1 j));
    obtain ⟨x,i,a⟩:=i; obtain ⟨z,j,b⟩:=j; obtain ⟨x,rfl⟩: ∃ y,wrap f y=x:= ⟨lift x,wrap_lift _⟩; obtain ⟨z,rfl⟩: ∃ y,wrap c y=z:= ⟨lift z,wrap_lift _⟩
    obtain ⟨j,rfl⟩:= axisEquiv.surjective j
    rw [vac_only i];
    have hQ(K:ℕ)(c:Side)(x:Cover)(y:TypeFace K)(a:G.ColorIndex): toneP G c K (ix (wrap c x,y) a)=ix (wrap c (pole y x),y) a:= by rw [tone_on]; exact congr_arg (fun x=>ix x a) (cover_mate ..)
    change _ = -installed X T (toneP G f 0 (ix (wrap f x,vac) _)) (toneP G c 1 (ix (wrap c z,coord j) _)); rw [hQ,hQ,show pole vac x= -x by simp [pole,brim,vac],ix, ix, tunnel, tunnel]; -- tactic syntax
    erw [← (twin (coord j)).tsum_eq (fun i:Cover=> if wrap c (pole (coord j) z)=wrap c i then localeV T (-x) (vac,a) (coord j,b) i else 0),← tsum_neg]; refine tsum_congr fun y=>?_ 
    simp only [tw_p,(show wrap c (pole (coord j) z)=wrap c (pole (coord j) y) ↔ wrap c z=wrap c y by simp [pole])]; split; exact compensates (T:=T) h hp _ _ _ _ _; exact (neg_zero ..).symm
end covariance
end YM.RG08.Invert
