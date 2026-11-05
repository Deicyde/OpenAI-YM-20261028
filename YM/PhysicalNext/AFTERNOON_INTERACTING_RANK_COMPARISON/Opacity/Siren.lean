import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Opacity.Scrutiny
/-!
# Pellet sufficient conditions

Use ALL endpoints projections and true V. No gauge or sign invariant requirement
on B/W reads: can symmetrise exponents ON the matched domain before expanding.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.InteractingRank.Pump
open Function Lattice RG Pressure Tree Wilson AnalyticBridge.GaussianFieldAlignment Locations Channels
open Matrix Finset PhysicalGuard7f546.Curved Next.SectorChange Precision AnalyticBridge.LocalGaussianLaws Filter
    SectorTools.PhysicalGaussianSwitch AnalyticBridge.RelativeLogdet Physical Push.Local MeasureTheory
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius
variable {c f : Side} {G : Gauge} {S : StepData c f} {x : ℝ} {A B : Stores S}
    {F F' : Forest S.ratio} {k k' : S.Choices} {U V : Config G c} {X X' : Support c} {p q : Pilot G S x}

structure Pulled {E : Type*} [MeasurableSpace E] (f : Pilot G S x→ E) (X : Support c) : Prop where
  enter (A : Stores S) (F : Forest S.ratio) (k : S.Choices) : ShellView (fun V y=> f ⟨A,F,k,V,y⟩)
  agreed ⦃p q : _⦄ : Matched p → Matched q → Hears X p q → f p=f q

def Tinted {E : Type*} (f : Pilot G S x→E):= ∀ p : Pilot G S x, Matched p → ∀ v,f (burnish v p)= f p

-- unrestricted structure used only for measuring *on* Matched.
namespace Pulled
section
variable {E E' : Type*} [MeasurableSpace E] [MeasurableSpace E'] {w : Pilot G S x→E}
lemma mono (h : Pulled w X) (hp : X⊆X'): Pulled w X':= ⟨h.enter,fun _ _ h' a q=>h.agreed h' a (advert q hp)⟩
lemma fetch (v : E) : Pulled (fun _:Pilot G S x=> v) X:= ⟨fun _ _ _=>⟨fun _=>v,measurable_const,fun _ _ _=>rfl⟩,fun _ _ _ _ _=>rfl⟩
lemma twine (h : Pulled w X) {g : E→ E'} (hg : Measurable g) : Pulled (fun x=>g (w x)) X := by
  refine ⟨fun A F k=> ?_,fun _ _ a b q=>congr_arg _ (h.agreed a b q)⟩
  obtain ⟨u,hu,hU⟩:= h.enter A F k; exact ⟨g ∘ u,hg.comp hu,fun V h y=>congr_arg g (hU V h y)⟩
lemma covers (h : Pulled w X) {w' : Pilot G S x→E'} (hg : Pulled w' X) : Pulled (fun x=>(w x,w' x)) X := by
  refine ⟨fun A F k=> ?_,fun _ _ a b q=>Prod.ext (h.agreed a b q) (hg.agreed a b q)⟩
  obtain ⟨u,hu,hU⟩:= h.enter A F k; obtain ⟨v,hv,hV⟩:=hg.enter A F k; exact ⟨fun a=>(u a,v a),hu.prodMk hv,fun V h y=>Prod.ext (hU V h y) (hV V h y)⟩
lemma plus [Add E] [MeasurableAdd₂ E] {v: Pilot G S x→ E} (h : Pulled w X) (hp : Pulled v X) : Pulled (fun x=> w x+v x) X:= (h.covers hp).twine (measurable_fst.add measurable_snd)
lemma times [Mul E] [MeasurableMul₂ E] {v: Pilot G S x→ E} (h : Pulled w X) (hp : Pulled v X) : Pulled (fun x=> w x*v x) X:= (h.covers hp).twine (measurable_fst.mul measurable_snd)
lemma sum {ι:Type} [AddCommMonoid E] [MeasurableAdd₂ E] {f: ι→ Pilot G S x→ E} (s : Finset ι) (h : ∀ i∈s,Pulled (f i) X) : Pulled (fun x=> ∑ i∈s,f i x) X:= by
  induction s using Finset.induction_on with
  | empty => simp; exact fetch 0
  | insert i s hi H=> simp_rw [sum_insert hi]; exact (h i (by simp)).plus (H fun j hj=> h j (by simp [hj]))
lemma prod {ι:Type} [CommMonoid E] [MeasurableMul₂ E] {f: ι→ Pilot G S x→ E} (s : Finset ι) (h : ∀ i∈s,Pulled (f i) X) : Pulled (fun x=> ∏ i∈s,f i x) X:= by
  induction s using Finset.induction_on with
  | empty => simp; exact fetch 1
  | insert i s hi H=> simp_rw [prod_insert hi]; exact (h i (by simp)).times (H fun j hj=> h j (by simp [hj]))
lemma countable {ι:Type} [Countable ι] {f: ι→ Pilot G S x→ ℝ} (h : ∀ i,Pulled (f i) X) : Pulled (fun p=> ∑' i,f i p) X:= by
  refine ⟨fun A F k=> ?_,fun _ _ a b q=>tsum_congr fun i=>(h i).agreed a b q⟩
  choose v hv H using fun i=> (h i).enter A F k; exact ⟨fun p=>∑' i,v i p, Measurable.tsum hv,fun V h y=> tsum_congr fun i=> H i V h y⟩
lemma leading (h : Pulled w X) (e : Wheel c) : Pulled (fun x=>w (spires e x)) (pushed e X):= by
  refine ⟨fun A F k=>?_,fun _ _ a b q=> h.agreed (a.signed e) (b.signed e) (lap e q a b)⟩
  let s:=e.1; let b:=e.2
  obtain ⟨u,hu,hU⟩:= h.enter (book s b A) (Locations.forest s b F) (ticket s b k)
  let Y:=fun p : Config G c × RoomView A x F G=> cusps A F s b x p.1 p.2
  have hg : Measurable Y:= by
    refine Measurable.prodMk (measurable_pi_lambda _ fun i=> ?_) (measurable_pi_lambda _ fun i=>?_)
    · change Measurable fun p : Config G c × RoomView A x F G=> rollY s b x A F p.2.1 i
      unfold rollY; split <;> fun_prop
    let g:= fun p : Config G c × RoomView A x F G => fiber s b p.1 S i.1.val.val (tape p.2.2 (Locations.active s b A F x i.1))
    have he : Measurable g := by
      have hu : Continuous (replica S.ratio (G:=G)):= continuous_pi fun i=>by unfold replica; split <;> fun_prop
      let J:= fun p:Config G c × RoomView A x F G=> tape p.2.2 (Locations.active s b A F x i.1)
      have he : Measurable J:= ((measurable_pi_apply _).comp tape.measurable).comp (measurable_snd.comp measurable_snd)
      unfold g fiber scatter
      split
      · let o:= i.1.val.val; let z:=sendEdge s (S.ratio.embed b) o
        have hw : Measurable (fun p : Config G c × RoomView A x F G=> (replica S.ratio p.1 z)⁻¹) := Measurable.inv (((measurable_pi_apply z).comp hu.measurable).comp measurable_fst)
        change Measurable fun p : Config G c × RoomView A x F G=> -(G.adjoint (replica S.ratio p.1 z)⁻¹) (J p)
        exact (Dictionary.FieldJet.adjoint_continuous.measurable.comp (hw.prodMk he)).neg
      exact he
    change Measurable fun p : Config G c × RoomView A x F G=> fan A F s b x p.1 p.2.2 i
    rw [show (fun p : Config G c × RoomView A x F G=> fan A F s b x p.1 p.2.2 i)=fun p=>g p i.2 from funext fun z=>congr_arg (fun a:G.Color=>a i.2) (Orthogonal.move_tape ..)]
    exact ((show Continuous fun a:G.Color=> a i.2 from PiLp.continuous_apply ..).measurable).comp he
  let R:= fun p : Config G c × RoomView A x F G => (pull s b p.1,Y p)
  exact ⟨u ∘ R, hu.comp (((continuous_pull ..).measurable.comp measurable_fst).prodMk hg), fun V hv y=> hU _ (turns_marks s b A V _ hv) _⟩
lemma versed (h : Pulled w X) (he : Tinted w) (O : Orchard S) (p : Prop) (τ) : Sees (fun A k U y=> w ⟨A,k.wood,k.tag,U,y⟩ : Shader G S x O E) X p τ := by
  refine ⟨fun A k=>h.enter A k.wood k.tag, fun hp hq H _ _ _ ht=> h.agreed hp hq (recall H ht hp hq),fun k v m z=>?_⟩
  exact (he ⟨_, k.wood,k.tag,_,z⟩ m v).symm
end
end Pulled
end YM.PhysicalNext.InteractingRank.Pump
