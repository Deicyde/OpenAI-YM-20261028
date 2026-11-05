import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Cadre.Aurora
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Daisy.Kiln

set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Cash
open PhysicalNext.Repeat.Greenbelt PhysicalNext.Repeat
open Filter Function Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Control Window Census Green Mask Pulse Itinerary Coat
open Packets Presented LabelSum Sector SliceRows.DataKernel LocalRows Footprint Raw ProbabilityTheory Poll Pond Matter
open Gas Ursell Trees Multiple Letter OmitClusters
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {P : Teller G} {c f : Side} {S : StepData c f} {T : Tube G S} {F : Tree.Forest S.ratio}
variable {a α W μ C δ e : ℝ} {R : Rep G f} {Z Z' : Support c} {L : Side}
variable {k k' : Finset ℕ} {w v : Air f G}
variable {j b l d : ℕ}
variable {Q : YM.ConnectedActivityE6.Target G P} {o : Target.Order G W}
variable (H : Cash W α μ L Q o C T R) (χ : Chi) (V : Config G c)
variable (p : Renewed j a δ e H)


variable (g : Molecule S→ℝ)
def trainedMill (c : Clusters H.ThinP) := Gas.term H.seam (H.entriesMill g) c
def homesteadMill := Gas.total H.seam (H.entriesMill g)
def lossesMill (A : Finset H.ThickP) := Gas.missing H.smallAt (H.tall A) (H.entriesMill g)
def siegeMill (A : Finset H.ThickP) := H.bankedMill V g A* H.homesteadMill g* Real.exp (-∑' i,H.lossesMill g A i)

variable (O : Tree.Forest S.ratio)
variable {f' : Molecule S→ℝ} {u' : ℝ} (hTag:H.TaggedW g)
    (hU : HasSum (fun i=> overhead (prism T α χ o.K V O) R Q.table * H.festo V g i) u')
include hU hTag
lemma coast_inMill : HasSum (fun i=> overhead (prism T α χ o.K V O) R Q.table * H.inletMill V g i) u' := by

  let v : Finset (Molecule S) → ℝ := fun t=> overhead (prism T α χ o.K V O) R Q.table*H.festo V g t
  have hv : HasSum v _:= hU
  have hp z (hp : z∉Set.range H.binders) : v z=0 := by
    by_contra hy; apply hp
    have he j (hj : j∈z) : (H.unionP j).Nonempty := by
      have hn := right_ne_zero_of_mul hy; unfold festo at hn; split at hn
      next hk => exact (hTag _ (fun h=> hn (prod_eq_zero hj h))).2
      exact (hn rfl).elim
    let X:= z.subtype fun i=> (H.unionP i).Nonempty ∧ (roster i).flags.Nonempty
    let Y:= z.subtype fun i=> (H.unionP i).Nonempty ∧ (roster i).flags=∅
    refine ⟨⟨X,Y⟩,?_⟩; unfold binders; ext i; change i∈H.stave X∪H.sword Y ↔ _; rw [mem_union]; constructor
    · rintro (hx|hx)
      all_goals obtain ⟨i,hi,hx⟩ := mem_map.mp hx; rw [← hx]; exact mem_subtype.mp hi
    intro hi; by_cases hp : (roster i).flags.Nonempty
    · exact Or.inl (show i∈H.stave X from mem_map_of_mem (Embedding.subtype _) (show (⟨i,he i hi,hp⟩:H.ThickP)∈X from mem_subtype.mpr hi))
    exact Or.inr (show i∈H.sword Y from mem_map_of_mem (Embedding.subtype _) (show (⟨i,he i hi,Finset.not_nonempty_iff_eq_empty.mp hp⟩:H.ThinP)∈Y from mem_subtype.mpr hi))
  have hx : HasSum (v∘ H.binders) _ := (H.bindInj.hasSum_iff hp).2 hv
  simp_rw [family_mill H V g hTag]; exact hx

omit hU hTag
variable {t x s q : ℝ}(hb:Ready H.smallAt (radiusB α) (fun i=> ‖H.entriesMill g i‖) a t e x)(hf: Summable (H.depositsMill g))(he:0≤a)
include hb he
lemma threshold_logMill : Real.log (H.homesteadMill g)= logSum H.seam (H.entriesMill g) ∧
    Real.exp (logSum H.seam (H.entriesMill g))= H.homesteadMill g :=
  let h:=price_log H.seam (H.entriesMill g) H.hardH H.smallAt (radiusB α) H.testS he (hb)
  ⟨h.2.2.2.2,h.2.2.1⟩

include hU hTag
lemma rampartMill : HasSum (fun A => overhead (prism T α χ o.K V O) R Q.table * H.siegeMill V g A) u' := by
  have hh := H.coast_inMill χ V g O hTag hU
  have ha A := (price_log H.seam (H.ignoresMill g A) H.hardH H.smallAt (radiusB α) H.testS he
    (show Ready _ _ _ _ t e x from ?_)).1.2.1.of_norm.hasSum
  swap
  · obtain ⟨hz,hv,hA,hD,hF,hY⟩:= hb
    exact (show Ready H.smallAt (radiusB α) (fun i=> ‖H.ignoresMill g A i‖) a _ _ _ from
      ⟨hz,hv,hA,hD,(fun _=>norm_nonneg _), Labels.raise_prices _ _ (fun _=> norm_nonneg _) hY (fun i=> by
        unfold ignoresMill Gas.cut; split
        · exact le_rfl
        rw [norm_zero]; exact norm_nonneg _)⟩)
  refine hh.prod_fiberwise fun A=> ?_
  have hz := (restores_log H.smallAt (H.tall A) (radiusB α) (H.entriesMill g) (fun i=>i.2.1) he
    (hb)).1
  convert! (((ha A).mul_left (H.bankedMill V g A)).mul_left (overhead (prism T α χ o.K V O) R Q.table)) using 2
  unfold siegeMill; rw [mul_assoc]; exact congr_arg _ hz.symm



omit hU hTag hb he
def cologneMill : H.Chapter→ℝ := Sum.elim (H.depositsMill g) fun i=> -(H.trainedMill g i)

def truthfulMill (c : H.Chainbook) := if H.Fresh c ∧ H.inventory c.1.toLeft=RG.flags (Pressure.temp α) V then
    manyW (H.cologneMill g) c else 0

lemma truthMill (A : Finset H.ThickP) (s : Reps H.fragrances) :
    H.truthfulMill V g (hint (A,s))=H.bankedMill V g A*manyW (fun i=>-(H.lossesMill g A i)) s := by
  let Z:= H.tall A
  let f i:= H.trainedMill g i
  let gZ i := H.lossesMill g A i
  let c := hint (A,s)
  have hh : c.1.toLeft=A := toLeft_disjSum ..
  have hx : c.1.toRight=s.1 := toRight_disjSum ..
  have hv i : gZ i= if Disjoint Z (H.bookFoot (.inr i)) then 0 else f i := rfl
  unfold truthfulMill; rw [hh]
  by_cases he : H.inventory A=RG.flags (Pressure.temp α) V
  swap; · unfold bankedMill; rw [if_neg (fun h=>he h.2),if_neg he,zero_mul]
  by_cases h : Gas.separated (blocked H.largeAt) A
  swap
  · unfold bankedMill Gas.value; rw [if_pos he,if_neg h,if_neg (fun hz=> h (hh ▸ hz.1.2.1)),zero_mul]
  unfold bankedMill Gas.value; rw [if_pos he,if_pos h]
  by_cases hk : ∀ i∈s.1, ¬Disjoint Z (H.bookFoot (.inr i))
  · have hn : H.Fresh c := ⟨hinter _, hh.symm ▸ h,fun i hi=> (by rw [hh]; exact hk i (hx ▸ hi))⟩
    rw [if_pos ⟨hn,he⟩, cologneMill, Letter.hint_price]; refine congr_arg _ ?_
    unfold manyW; apply prod_congr rfl; intro i _; dsimp only; rw [show H.lossesMill g A i.val=f i.val from (hv i.val).trans (if_neg (hk i.val i.2))]
  rw [if_neg (fun hn=> hk (fun i hi=> (show ¬ Disjoint (H.tall A) _ from hh ▸ hn.1.2.2 i (hx.symm ▸ hi)))), manyW]
  push Not at hk; obtain ⟨i,hi,hk⟩ := hk
  rw [Finset.prod_eq_zero (s:=univ) (i:= (⟨i,hi⟩:↥s.1)) ?_ ?_,mul_zero]
  · simp
  change (-gZ i)^_/ _=0; rw [hv,if_pos hk]; simp

include hb he hf
lemma savableMill : Summable (H.truthfulMill V g) := by
  have hk' := hb
  have hv : Summable (H.trainedMill g) := ((price_log H.seam (H.entriesMill g) H.hardH H.smallAt (radiusB α) H.testS
    he hk').2.1.2.1).of_norm
  have hg : Summable (H.depositsMill g) := by
    exact hf
  have hs := (concert (show Summable (H.cologneMill g) from Summable.sum _ hg hv.neg)).summable
  apply Summable.of_norm_bounded hs.norm; intro i; unfold truthfulMill; split
  · exact le_rfl
  rw [norm_zero]; exact norm_nonneg _

include hTag hU
lemma bouquetMill : HasSum (fun c : H.Chainbook=> overhead (prism T α χ o.K V O) R Q.table * H.homesteadMill g * H.truthfulMill V g c) u' := by
  let K:= overhead (prism T α χ o.K V O) R Q.table; let f c := K * H.homesteadMill g*H.truthfulMill V g c
  have hg (A : Finset H.ThickP) : HasSum (fun v=> f (hint (A,v))) (overhead (prism T α χ o.K V O) R Q.table * H.siegeMill V g A) := by
    have he' := missing_tail H.smallAt (H.tall A) (radiusB α) (H.entriesMill g) (fun i=> i.2.1) he
      (hb) 0
    simp only [Nat.zero_le,↓reduceIte] at he'
    have hz : Summable (H.lossesMill g A) := he'.2.1.of_norm
    have hy := (concert hz.neg).mul_left (K*H.homesteadMill g * H.bankedMill V g A)
    convert! hy using 1
    · funext i; unfold f; rw [H.truthMill V g]; ring
    unfold siegeMill; rw [tsum_neg]; unfold K; ring
  have ht : Injective (@hint H.ThickP H.fragrances) := LeftInverse.injective (show LeftInverse Letter.hidden hint from
    (tracks (κ:=H.fragrances) (ι:=H.ThickP)))
  have hv : Summable (f∘hint (ι:=H.ThickP)) := ((H.savableMill V g hb hf he).mul_left _).comp_injective ht
  apply (ht.hasSum_iff (f:=f) ?_).1
  · rw [← (H.rampartMill χ V g O hTag hU hb he).tsum_eq]; simp_rw [← (hg _).tsum_eq];
    exact (show (∑' i,(f ∘ hint (ι:=H.ThickP)) i)= _ from hv.tsum_prod) ▸ hv.hasSum
  intro i hp; unfold f truthfulMill; rw [if_neg (fun hx=> hp ⟨Letter.hidden i,Letter.unruly _ hx.1.1⟩),mul_zero]




omit hU hTag hb hf he
def smilesMill (r : H.Chainbook) := if H.Fresh r ∧ Ac.Spark H.bookFoot r.1 ∧ H.statesPool V r then
    manyW (H.cologneMill g) r else 0

def canopyMill (U : Finset H.Chainbook) := if Letter.Valid H.bookFoot U ∧ H.eruptedPool V U then ∏ r∈U,H.smilesMill V g r else 0

private lemma tiesD (U : Finset H.Chainbook) (h : Letter.Valid H.bookFoot U) : H.Fresh (openRep U) ↔ ∀ r∈U,H.Fresh r := by
  let b:= openRep U
  have hu (i) (hi : i∈U) : i.fst⊆ b.fst := fun j hj=> (Letter.stages _ U).mpr ⟨i,hi,hj⟩
  have hx (i j) (hi : i∈U) (hj : j∈U) (p) (hh : p∈H.library i) (hi' : p∈H.library j) : i=j := by
    by_contra H; exact Finset.disjoint_left.mp (h.disjoint hi hj H) hh hi'
  constructor
  · intro he i hi
    refine ⟨fun a ha=> (Letter.lifting U h.addresses i hi _ ha).symm.trans (he.1 a (hu i hi ha)), ?_, ?_⟩
    · exact fun j hj k hk=> he.2.1 j ((H.orbiting U j).2 ⟨i,hi,hj⟩) k ((H.orbiting U k).2 ⟨i,hi,hk⟩)
    intro j hj
    obtain ⟨v,hv,hj'⟩ := not_disjoint_iff.mp (he.2.2 j (mem_toRight.mpr <| hu i hi (mem_toRight.mp hj)))
    obtain ⟨u,hU,hv⟩ := mem_biUnion.mp hv; obtain ⟨m,hm,hv'⟩ := (H.orbiting U u).1 hU
    have ht : v∈H.library i := mem_biUnion.mpr ⟨Sum.inr j,mem_toRight.mp hj,hj'⟩
    have hb : i=m := hx i m hi hm v ht (H.arching hv' hv)
    exact not_disjoint_iff.mpr ⟨v,mem_biUnion.mpr ⟨u,hb.symm ▸ hv',hv⟩,hj'⟩
  intro hp; refine ⟨?_,?_,?_⟩
  · intro i hi; obtain ⟨z,hz,hZ⟩ := (Letter.stages _ U).mp hi
    exact (Letter.lifting U h.addresses z hz _ hZ).trans ((hp _ hz).1 i hZ)
  · intro i hi j hj hk
    obtain ⟨u,hu,hU⟩ := (H.orbiting _ i).1 hi
    obtain ⟨v,hv,hV⟩ := (H.orbiting _ j).1 hj
    by_cases hf : u=v
    · exact (hp u hu).2.1 i hU j (hf.symm ▸ hV) hk
    apply not_or.mpr; refine ⟨hk,?_⟩
    rintro ⟨s,hs,ht⟩; exact hf (hx u v hu hv s (H.arching hU hs) (H.arching hV ht))
  intro i hi; obtain ⟨u,hu,hx⟩ := (Letter.stages _ U).mp (mem_toRight.mp hi)
  obtain ⟨j,hj,hi'⟩ := Finset.not_disjoint_iff.mp ((hp u hu).2.2 i (mem_toRight.mpr hx))
  obtain ⟨x,hj,hz⟩ := mem_biUnion.mp hj
  exact not_disjoint_iff.mpr ⟨j,mem_biUnion.mpr ⟨x,(H.orbiting ..).2 ⟨u,hu,hj⟩,hz⟩, hi'⟩

lemma book_associatedMill (U : Finset H.Chainbook) (h : Letter.Valid H.bookFoot U) :
    H.canopyMill V g U=H.truthfulMill V g (openRep U) := by
  unfold canopyMill truthfulMill; simp_rw [← show H.eruptedPool V U ↔ H.inventory (openRep U).1.toLeft= RG.flags (Pressure.temp α) V from H.allotment (prism T α Chi.canonical o.K V (Classical.choice (Tree.select S.ratio S.patch.odd_side))) U, tiesD H U h]
  by_cases he : H.eruptedPool V U
  · rw [if_pos ⟨h,he⟩]; split
    next hx => rw [prices_union h.addresses]; apply prod_congr rfl; intro i hi
               exact if_pos ⟨hx.1 i hi,h.classified i hi,H.colonies (prism T α Chi.canonical o.K V (Classical.choice (Tree.select S.ratio S.patch.odd_side))) U h he i hi⟩
    next hx =>
      by_contra hp; exact hx ⟨fun i hi=> by
        by_contra hg; exact hp <| prod_eq_zero hi (show H.smilesMill V g i=0 from if_neg fun h=> hg h.1), he⟩
  rw [if_neg (fun h=>he h.2),if_neg (fun h=>he h.2)]

include hU hTag hb hf he
lemma convoyMill : HasSum
    (fun U => overhead (prism T α χ o.K V O) R Q.table * H.homesteadMill g * H.canopyMill V g U)
    u' := by
  let f U:= overhead (prism T α χ o.K V O) R Q.table * H.homesteadMill g * H.canopyMill V g U
  let b (c) := shard H.bookFoot c
  have hx : Injective b := LeftInverse.injective (show LeftInverse openRep b from fun r=> inflates H.bookFoot r)
  apply (hx.hasSum_iff (f:=f) ?_).1; swap
  · intro x ht; unfold f canopyMill; rw [if_neg (fun h=>ht ⟨openRep x,Letter.includes H.bookFoot x h.1⟩),mul_zero]
  have hv c : f (b c)=overhead (prism T α χ o.K V O) R Q.table * H.homesteadMill g * H.truthfulMill V g c := by
    unfold f b; rw [H.book_associatedMill V g (Letter.shard H.bookFoot c) (sharding H.bookFoot c), inflates]
  simp_rw [Function.comp_def,hv]; exact H.bouquetMill χ V g O hTag hU hb hf he

end YM.ConnectedActivityE6.Cash
