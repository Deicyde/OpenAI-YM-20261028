import YM.RG08.Roost.Driver
/-! # Exact flight of post-step residuals and any combination
 of unmarked laws under Gauge, turnover incl inverse. -/
noncomputable section
set_option autoImplicit false
namespace YM.RG08.Roost
open Filter Function Matrix MeasureTheory Finset Lattice Exterior Wilson RG Precision Stationary Work.F05 Tree Carrel Prism Tack Camera Slate Gallery
open Forms Rudder Anchor Isles Laurent Pert.Bulk Mount Glyph Room Bloch Quarry Aggregate Steam
open scoped Classical Matrix ContDiff Topology BigOperators InnerProductSpace PowerSeries ENNReal Matrix.Norms.Frobenius
variable {c f:Side}{G:Gauge}{P:Patch}{K:KernelChoices}(h:P.Branches K G)(A B:Bed){C:Castle G}{Z:ChartRatio G}
lemma reserves(c:Side){I:Type}[Fintype I](hC:Mount.Stable C)(s t:Tray (Market (Loc G 1)))(d:Signed)
    (v:Lines G c 1→I)(w:Strip (Lines G c 1) I)(hw:∀ i,Pace (w i))(he:roll w 0=0)(p:I→Dig)
    (hh:∀ i,p (v i)=(Gallery.native c s).get i)(hp:∀ i,breath p (Quarry.eye (w i))=(Gallery.native c t).get i)
    (hv:∀ᶠ x:Cellar I in 𝓝 0, ∃ r:Site c→G.El, represent (borne id (roll w x))=Lattice.gauge r (pull d 0 (represent (borne v x)))):
    let V:=stock (unveil (demand C) c);breath (Gallery.native c s).get V=breath (Gallery.native c t).get V:=by
 intro V
 let q:Strip (Lines G c 1) I:=fun i x=>x (v i)
 have hM:belt (rescaleFields q) V=belt (rescaleFields w) V:=overt hC c d _ _ (fun _=>(contDiff_apply ℝ ℝ _).contDiffAt) hw rfl he (by
   have ht (y r' ):offers G (y ∘ r':Cellar (Lines G c 1))=represent (borne r' (y:Cellar I)):=by funext i;rw [Work.F03.represent_link];rfl
   filter_upwards [hv] with x hx
   obtain ⟨r,hr⟩:=hx; refine ⟨r,?_⟩
   have hW :offers G (roll w x)= represent (borne id (roll w x)):=by funext i;rw [Work.F03.represent_link];rfl
   rw [hW,hr]; exact congrArg _ (congrArg (Lattice.pull d 0) ((ht x _).symm)) -- roll q defeq x ∘ v
 )
 have hA:= congrArg (breath p) hM;rw [fugue,fugue] at hA
 change breath (fun j=>breath p (Quarry.eye (q j))) _=breath (fun i=>breath p (Quarry.eye (w i))) _ at hA
 unfold q at hA;simp_rw [hp,eye_reader,bases_x,hh] at hA;exact hA
-- reuse with pict
lemma tutors (hC:Mount.Stable C): Academy (demand C):=by
 intro x u d
 let y:= art x u
 apply Gallery.anchor (landing hC) Isles.rise
 filter_upwards [rear (hot d) y Isles.rise] with n hn
 let c:=Isles.chain n
 refine reserves c (I:=Cove c (cuff G)) hC _ _ 1 (Quarry.badge _) (fun i x=> arch (Quarry.badge c) (raise c d) x i) (contDiffAt_pi.mp (zoom ..)) (show arch (Quarry.badge c) (raise c d) 0=0 from funext fun i=>by unfold arch;rw [map_zero,tub_nigh];rfl) ((Gallery.native c y).get) (fun _=>rfl) (fun q=>?_) ?_
 · exact (prophet (c:=c) d q id _).trans (hn q).symm
 · filter_upwards [enfold (Quarry.badge c) (raise c d)] with x hx; refine ⟨(raise c d).act x,?_⟩; rw [pull_id]; exact hx

lemma strands (hC:Mount.Stable C): SignedLaw (demand C):=by
 intro d x
 apply Gallery.anchor (landing hC) Isles.rise
 filter_upwards [spin_reach d x] with n hn
 let c:=Isles.chain n
 let p :=(Gallery.native c x).get
 refine reserves c (I:=Lines G c 1) hC _ _ d id (fun i t=> Quarry.blade d t i) (contDiffAt_pi.mp (bladed ..)) (blade0 d) p (fun _=>rfl) ?_ ?_
 · intro q
   let a:=supply d q.2;let i:=Carrel.badge (P:=c) d q
   exact (haven p a i).trans (hn q).symm
 exact Filter.Eventually.of_forall (fun x=>⟨1,by change represent (borne id (blade d x))=_;rw [show represent _=pull d 0 (represent (borne id x)) from blade_close d x];funext; simp [Lattice.gauge]⟩)

variable {I:Type} {k:ℕ}
lemma all_volume (f g:Flake k I)(w:Tray I):Gallery.volume (f+g) w=Gallery.volume f w+Gallery.volume g w:=by unfold Gallery.volume; simp only [Pi.add_apply,add_smul,Finset.sum_add_distrib]
lemma all_announced (F H:Gallery.Script I)(w:Tray I): announced (F+H) w=announced F w+announced H w:=by
 ext n :1; unfold announced dubbed; simp only [tap,PowerSeries.coeff_mk,Pi.add_apply,all_volume,Finset.sum_add_distrib,map_add]
-- normalization and subtraction for post prescriptions (announced linear).
lemma nil_announced (w:Tray I):announced 0 w=0:=by ext e;simp [announced,dubbed,Gallery.volume,tap]
structure AcademyL (V:Gallery.Script (Market (Loc G 1))) : Prop where
 soft: Academy V
 form: SignedLaw V
lemma AcademyL.zero : AcademyL (G:=G) 0:=⟨fun _ _ _=> (nil_announced _).trans (nil_announced _).symm,fun _ _=> (nil_announced _).trans (nil_announced _).symm⟩
lemma AcademyL.add {V W: Gallery.Script (Market (Loc G 1))}(h:AcademyL V)(ht:AcademyL W): AcademyL (V+W):=⟨fun x u d=>by rw [all_announced,all_announced,h.soft x u d,ht.soft x u d],fun d x=>by rw [all_announced,all_announced,h.form d x,ht.form d x]⟩
lemma AcademyL.neg {V:Gallery.Script (Market (Loc G 1))}(h:AcademyL V): AcademyL (-V):=by
 have he{X:Type}(V:Gallery.Script X)(x:Tray X): announced (-V) x= -announced V x:=eq_neg_of_add_eq_zero_left (by rw [←all_announced,neg_add_cancel,nil_announced])
 constructor
 · intro x a d; rw [he,he,h.soft x a d]
 intro d x;rw [he,he,h.form d x]
lemma AcademyL.sub {V W:Gallery.Script (Market (Loc G 1))}(h:AcademyL V)(ht:AcademyL W): AcademyL (V-W):=sub_eq_add_neg V W ▸ h.add ht.neg
lemma prayers (p:Foyer P K A B C Z): AcademyL (vault G P K h C Z A B):=⟨lectern _ _ _ _ _ _ _ p,spectacles h A B _ _ p⟩
lemma masters (hC:Mount.Stable C): AcademyL (demand C):=⟨tutors hC,strands hC⟩
lemma frontier (V:Gallery.Script (Mix G.ColorIndex 1))(e:ℕ)(h:AcademyL V)(ht:∀ k<e,∀ i≠0,V k i=0)(hp:k ≤ e+2)(hs:Forms.Sym (V e k))(hM:Cohort (V e k)){σ p:ℝ}(he:Held (carpet _) σ p (V e k)) : let F:=Anchor.extend 1 (V e k);Symmetry.Cloak (Symmetry.dressed G k) 1 F ∧ Closing F ∧ Held (carpet _) σ p F:=tickets V e (schools V h.soft e).1 (sunglasses V h.form e) (schools V h.soft e).2 ht hp hs hM he
end YM.RG08.Roost
