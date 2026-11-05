import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Opacity.Greens
import YM.Push.STRESS_FLUX.Line
import YM.UVNext.COMMON_GRADE_ASSEMBLY.Campaign
/-!
# Value readout for the opaque body

Finite regrade accepts primitive inputs via an exponential; doesn't constrain individual primitive sign and gauge. Tag paint convention here real. Use ShellView contract; discounts only for Actual `p.bp`. Not using `All` authorization for E branches. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.InteractingRank.Pump
open Function Lattice RG Pressure Tree Wilson AnalyticBridge.GaussianFieldAlignment Locations Channels
open Matrix Finset PhysicalGuard7f546.Curved Next.SectorChange Precision AnalyticBridge.LocalGaussianLaws Filter
    SectorTools.PhysicalGaussianSwitch AnalyticBridge.RelativeLogdet MeasureTheory
    Push.SectorMeasure Push.SectorMeasure.Oriented Push.AbsoluteSums Pressure.Stores
    AnalyticNext.ConnectedActivity GaugeRoute Display.Sew Pot
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius
variable {c f : Side} {G : Gauge} {S : StepData c f} {x W : ℝ} {A B : Stores S} {v : Dyed G S} {P : Teller G}

structure Plate (v : Dyed G S) (x W : ℝ) where
  base : Core S x → Pilot G S x → ℝ
  aux : Glade c→ Pilot G S x → ℝ
  current i : Pulled (base i) (acre i)
  fuel i : Tinted (base i)
  tip i : Pulled (aux i) i.val
  mine i : Tinted (aux i)
  lot i p e : base (hoop S x e i) (spires e p) = base i p
  toll e p i : aux (garden (orient e) i) p=aux i (spires e p)
  pitch p (hp : Matched p) : v.Playing W p → v.spoolLift p = (∑ i∈owners p.key x, base i p)+∑ i,aux i p

-- produce when E posts estimates actual. Gauge sym suppression affordability PROVEN already in Light. This consumes total during sign turns, locations of all arrows cover-cardinal equal.
def routes (c : Side) : Sheet (fun i:Glade c=>i.val) where
  dial e:= garden (orient e)
  work e q i:= by
    apply Subtype.ext
    change pushed (meet e q) _=pushed e (pushed q _); unfold pushed; simp_rw [Finset.map_eq_image, Finset.image_image]
    congr 1; exact funext fun _=>together e q _
  extend e i:= rfl
private lemma integrates (H : Finset (Core S x)) (p : Pilot G S x) (hp : Matched p) (F : Core S x→Pilot G S x→ℝ) (f' : Glade c→Pilot G S x→ℝ) (ha : ∀ i,Pulled (F i) (acre i)) (hr : ∀ i,Pulled (f' i) i.val) (hx : ∀ i,Opaque (F i)) (he : ∀ i,Opaque (f' i)) (z : ℝ)
    (h : ∀ (e : Wheel c) (w:Site c→G.El),(∑ i∈H.map (hoop S x e).toEmbedding,F i (burnish w (spires e p)))+(∑ i,f' i (burnish w (spires e p)))=z) : (∑ i∈H,fill scope F i p)+(∑ i,fill (routes c) f' i p)=z:= by
  rw [full scope F ha hx H p hp, full (routes c) f' hr he univ p hp,← sum_add_distrib, ← show ∑ _i:Wheel c,cash_at c*z=z from by rw [← sum_mul, cash_one,one_mul]]
  refine Finset.sum_congr rfl fun i _=>?_ ; rw [← mul_add]; congr 1
  have hf: (univ.map (((routes c).dial i).symm).toEmbedding)=univ:= by ext; simp
  rw [hf, ← integral_add]
  · change (∫ v,((∑ j∈H.map (hoop S x i).toEmbedding, F j (burnish v _))+∑ j,f' j (burnish v _)) ∂piHaar G (Site c))=z; simp_rw [h]; simp
  · exact integrable_finsetSum _ fun j _=> patch_part (ha j) (hx j) (hp.signed i)
  exact integrable_finsetSum _ fun j _=> patch_part (hr j) (he j) (hp.signed i)

variable {o n Λ δ w a C η b₀ : ℝ}
def brushes (F : Core S x→Pilot G S x→ℝ) (f' : Glade c→Pilot G S x→ℝ) (ha : ∀ i,Pulled (F i) (acre i)) (hr : ∀ i,Pulled (f' i) i.val) (hx : ∀ i,Opaque (F i)) (hy : ∀ i,Opaque (f' i))
    (hY : ∀ p,Matched p → v.Playing W p → (∑ i∈owners p.key x,F i p)+(∑ i,f' i p)=v.spoolLift p)
    (ht : Boosted v.things P x) (hp : Physical.Certified S v.things x a C η b₀) (hs : v.things.up=v.source.path) (hc : v.things.high=v.source.clip) (hJ : LocalRatio v.ratio)
    (hd : 0<v.arc) (hD :4*v.arc<v.ratio.radius) (hR : v.source.Lawful o n Λ δ w) (hb : 0<v.source.beta) (hΘ : v.bp.threshold=temp x) : Plate v x W where
  base := fill scope F
  aux := fill (routes c) f'
  current i:= (fill_price scope F ha i).1
  fuel i:= (fill_price scope F ha i).2.1
  tip i:= (fill_price (routes c) f' hr i).1
  mine i:= (fill_price (routes c) f' hr i).2.1
  lot i p e:= by
    rw [← (fill_price scope F ha _).2.2 e]; exact congr_arg (fun i=>fill scope F i p) ((hoop S x e).symm_apply_apply i)
  toll e p i:= (fill_price (routes c) f' hr i).2.2 e p
  pitch p h hP:= by
    symm; apply integrates _ p h F f' ha hr hx hy
    intro e u; let y:= burnish u (spires e p)
    rw [← rotate_owners, show book e.1 e.2 p.key=y.key from rfl]; exact (hY _ ((h.signed e).bright u) (v.starlet W ht p h u e hP)).trans (v.sparkle e ht hp hs hc hJ hd hD hR hb hΘ p h u)
-- orientation lot intentionally at ALL pilots, Mail dims colored after Reps
namespace Pot
abbrev Rung (S : StepData c f) (x : ℝ) := {i:Core S x × Support f// i.2 ⊆ fields i.1}

def rips (i:Rung S x):= i.val.1
def markT (i:Rung S x):= i.val.2
def planting (O:Core S x) t (ht : t ⊆ fields O): Rung S x:=⟨(O,t),ht⟩

def traveling (S : StepData c f) (x : ℝ) (e : Wheel c) : Equiv.Perm (Rung S x) := Equiv.subtypeEquiv
    ((scope (S:=S) (x:=x)).dial e |>.prodCongr (orient (inflow S e)).finsetCongr) (fun i=> by
      rcases i with ⟨i,j⟩; change j ⊆ fields i ↔ (j.map _) ⊆ fields ((hoop S x e).symm i)
      have he := sends_field e ((hoop S x e).symm i); rw [Equiv.apply_symm_apply] at he; rw [← he]; exact Finset.map_subset_map.symm)
variable (v : Dyed G S) (W : ℝ) (M : Plate v x W)

def autumn (i : Core S x) (p : Pilot G S x):= Real.exp (M.base i p)*∏ j∈mined i,v.ask W p j

def checkIn (i : Rung S x) (p : Pilot G S x) := if markT i = hoes v (rips i) p then (1:ℝ) else 0
lemma planted_turn (h : P.Funds S v.things) (i : Rung S x) (p : Pilot G S x) (e : Wheel c): checkIn v i (spires e p) = checkIn v (traveling S x e i) p:= by
  unfold checkIn; apply if_congr _ rfl rfl
  let j:= (hoop S x e).symm (rips i); have he:=hoop S x e |>.apply_symm_apply (rips i)
  have ht := hoe_ship e v h j p; rw [he] at ht
  rw [← Finset.map_injective (orient (inflow S e)).toEmbedding|>.eq_iff]; -- may both
  exact Iff.of_eq (congr_arg ((markT i).map (orient _).toEmbedding= ·) ht)
lemma guard_paid (h : Boosted v.things P x) (hd : 0<v.arc) (hr : 2*v.arc<firstRadius G) (hm : 120≤radiusB x)
    (i : Rung S x): Pulled (checkIn v i) (acre (rips i)) ∧ Tinted (checkIn v i):= by
  let j:= rips i; let X:= acre j
  refine ⟨⟨fun A F k=>?_,fun p q _ _ ht=>?_⟩,fun p hp z=>?_⟩
  · obtain ⟨p,hp,H⟩:= v.top_read h hd hr A F k
    let s := fields j; let b:= markT i
    have he : MeasurableSet {y|b=s∩ flags v.source.p.threshold (p y)}:= by
      rw [show {y|b=s∩ flags v.source.p.threshold (p y)}= ⋃ (t:{t:Support f// b=s∩t}),{y|flags v.source.p.threshold (p y)=t.val} from ?_]
      exact MeasurableSet.iUnion fun t=> hp (flags_measurable_eq ..)
      ext i; simp only [Set.mem_setOf_eq, Set.mem_iUnion]; constructor
      · intro hi; exact ⟨⟨_,hi⟩, rfl⟩
      rintro ⟨j,h⟩; rw [h]; exact j.property
    refine ⟨(fun y=> if b=s∩ flags v.source.p.threshold (p y) then 1 else 0),Measurable.ite he measurable_const measurable_const,fun V hp y=> ?_⟩
    unfold checkIn hoes; dsimp only at H ⊢; rw [H V hp y]
  · unfold checkIn; apply if_congr _ rfl rfl; rw [show hoes v _ _=hoes v j q from ?_]
    refine RG.flags_agree _ _ _ _ ?_
    -- halo field readability even around fine flags.
    intro s hs he; apply v.peak_record ht _ h.ready
    obtain ⟨i,hi,hI⟩:= halo_spec.mp (Next.Rank.Thirst.inspect _ hs)
    obtain ⟨v,hv,hc⟩:= mem_biUnion.mp (show i∈ fields j from hi)
    have hu : S.ratio.parent i ∈ j.val.place:= mem_union_left _ (mem_union_left _ (mem_biUnion.mpr ⟨v,hv,mem_image_of_mem _ hc⟩))
    have hh : separation (S.ratio.parent i) (S.ratio.parent s.1) ≤ 8+1:= (Work.E04.parent_separation ..).trans (Nat.add_le_add_right hI 1)
    exact Shields.shift (o:=S.ratio.parent i) (t:=500*radiusB x) (fun k hk=> halo_spec.mpr ⟨_,hu,hk⟩) (by omega)
  unfold checkIn hoes; rw [Dyed.top_steam v h p hp,gauge_flags]

lemma booth_cape (h : Boosted v.things P x) (hm : Coverage.shutters S.patch+1 ≤ radiusB x) (hd : 0<v.arc) (hr : 2*v.arc<firstRadius G) (i : Core S x):
    Pulled (autumn v W M i) (acre i) ∧ Tinted (autumn v W M i) ∧ ∀ p (e : Wheel c), autumn v W M i (spires e p)=autumn v W M ((hoop S x e).symm i) p:= by
  refine ⟨Pulled.times ((M.current i).twine Real.continuous_exp.measurable) (Pulled.prod (mined i) ?_),fun p hp f=>?_,fun p e=>?_⟩
  · intro j hj; exact v.footage_read W j h hm hd hr (entry_point (by omega) hj)
  · unfold autumn; rw [M.fuel i p hp f]; exact congr_arg _ (prod_congr rfl fun j _ => (v.bootup W h p j f hp).symm)
  let j:= (hoop S x e).symm i; have hv:hoop S x e j=i:=Equiv.apply_symm_apply ..
  have h1:=M.lot j p e; have hz:= rotate_mines e j; rw [hv] at h1 hz
  unfold autumn; rw [h1]; apply congr_arg₂ HMul.hMul rfl; rw [← hz,prod_map]
  exact prod_congr rfl fun j _=> v.footship W e h.funded j p
end Pot
end YM.PhysicalNext.InteractingRank.Pump
