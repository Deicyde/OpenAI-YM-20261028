import YM.MultipleContact.Pair.Geometry
import YM.Work.A01.Support

/-! Bounded evaluation of physical fields on compact clear targets; using a provisional output before projecting on fixed detectors. -/
set_option maxHeartbeats 200000

set_option autoImplicit false
noncomputable section
namespace YM.MultipleContact.Two
open Function Filter Set Metric Finset Power Table
open scoped Topology Filter BigOperators ContDiff Classical
variable {G:Gauge}{L:Register G}{S:Table L}{n w:ℕ}

abbrev FamilyData (V:Type*) (L:Register G) := (e:Exterior L)→E4→Points e.n→V
def AtPrice {V:Type*}[NormedAddCommGroup V] (f:FamilyData V L) (p:ℝ):Prop:=∀e:Exterior L, ∀K:Set (Points e.n),IsCompact K → Room K → Asympt K (fun z y=>f e y z) p

lemma site_continuous (H:S.Smooth)(q:Fin n→L.Token) (w:ℕ)(u:E4)(z:Points n)(h:Safe u z)(v:S.Field w):ContinuousAt (fun p:E4×Points n×S.Field w=>siteValue S q w p.2.2 p.1 p.2.1) (u,z,v):=by
  let B:=Module.finBasis ℂ (S.Field w)
  have he (x:E4)(z:Points n)(v:S.Field w) : siteValue S q w v x z=∑ i,B.coord i v * siteValue S q w (B i) x z:=by
       let f:=Work.A01.frontRead (S.classTokens∘q) (Points.cons x z) w
       simp_rw [siteValue,fixedValue,← Work.A01.front_eval]; change f v =∑ i,B.coord i v*(f _)
       nth_rw 1 [← B.sum_repr v];rw [map_sum]; exact Finset.sum_congr rfl fun i _=> f.map_smul _ _
  rw [show (fun p:E4×Points n×S.Field w=>siteValue S q w p.2.2 p.1 p.2.1)=_ from funext fun p=>he p.1 p.2.1 p.2.2]
  refine tendsto_finsetSum Finset.univ (fun i _=> ContinuousAt.mul (by exact ((B.coord _).continuous_of_finiteDimensional.comp (continuous_snd.comp continuous_snd)).continuousAt) ?_)
  let f(x) := S.useAt S x (Fin.cons (⟨w,B i⟩:S.Tag) (S.classTokens ∘ q))
  let b(p:E4×Points n×S.Field w):=Points.cons p.1 p.2.1
  have hb:Continuous b := continuous_cons.comp (continuous_fst.prodMk (continuous_fst.comp continuous_snd))
  exact (((S.class_smooth S H _ _ h |>.contDiffAt ((conf_open _).mem_nhds h)).continuousAt).comp_of_eq hb.continuousAt rfl : ContinuousAt (f∘b) (u,z,v)) -- malformed colon fix
lemma site_bound_at (H:S.Smooth) (q:Fin n→L.Token)(k:ℕ)(K:Set (E4×Points n))(hK:IsCompact K)(hr : ∀p∈K, Safe p.fst p.snd) : ∃ c:ℝ,0≤ c∧ ∀p∈K,∀v:S.Field k, ‖siteValue S q k v p.1 p.2‖ ≤ c*‖v‖:=by
    let f(p:E4× Points n):=Work.A01.frontRead (S.classTokens ∘ q) (Points.cons p.1 p.2) k
    have hf(y:E4×Points n)(z):siteValue S q k z y.1 y.2=f y z := (Work.A01.front_eval _ _ _ z).symm
    suffices he:∃c:ℝ,0 ≤ c ∧ ∀p∈K, ∀v,‖f p v‖≤c*‖v‖ by obtain ⟨c,hc,hh⟩:=he; exact ⟨c,hc,fun p hp v=>by rw [hf];exact hh p hp v⟩
    refine linear_bound_compact (K:=K) hK f (continuousOn_of_forall_continuousAt (fun y hy=> ?_))
    let b : (E4×Points n) × S.Field k→E4×Points n × S.Field k:=fun x=>(x.1.1,x.1.2,x.2)
    have hb:Continuous b := (continuous_fst.comp continuous_fst).prodMk ((continuous_snd.comp continuous_fst).prodMk continuous_snd)
    have eq': (fun p: (E4×Points n) × S.Field k=>f p.1 p.2)=(fun p:E4×Points n×S.Field k=>siteValue S q k p.2.2 p.1 p.2.1) ∘ b := funext fun y=>(hf y.1 y.2).symm
    have hc : ContinuousAt (fun p : E4 × (Points n × _) => _) (b y) := site_continuous H q k y.1.1 y.1.2 (hr _ (Set.mem_prod.mp hy).1) y.2
    exact eq'.symm ▸ hc.comp hb.continuousAt

lemma site_bound (H:S.Smooth)(q:Fin n→L.Token)(k:ℕ)(K:Set (Points n))(hK:IsCompact K)(hr:Room K): ∃ c:ℝ,0≤ c ∧ ∀z∈K,∀v:S.Field k, ‖siteValue S q k v 0 z‖ ≤ c*‖v‖:=by
  obtain ⟨c,hc,he⟩:=site_bound_at H q k ({0}×ˢ K) (isCompact_singleton.prod hK) (by rintro ⟨x,z⟩ h; obtain rfl:x=0:=mem_singleton_iff.mp (Set.mem_prod.mp h).1;exact hr _ (Set.mem_prod.mp h).2)
  exact ⟨c,hc,fun z hz v=>he (0,z) (Set.mem_prod.mpr ⟨rfl,hz⟩) v⟩

variable (w) (D:Detector S w)
lemma pull_price {g:FamilyData ℂ L} {p:ℝ} (hg:AtPrice g p) : LocalBound (pull w D g) p :=by
   have H:=Asympt.pi (K:=(Set.univ : Set Unit)) (p:=p) (H:=fun _:D.probes=>ℂ) (fun e _ y=>g (e:Exterior L) y (relative (e:Exterior L))) (fun e=>?_)
   · exact H.linear_const D.decode
   exact (hg e.val _ (isCompact_singleton (x:=relative e.val)) (fun z hz => (mem_singleton_iff.mp hz).symm ▸ relative_safe e.val)).reindex Set.univ (fun _ _=>relative e.val) (by simp)
lemma center_price (H:S.Smooth) {s:E4→ S.Field w}{p:ℝ} (hs:LocalBound s p) : AtPrice (fun e y z=>siteValue S e.letter w (s y) 0 z) p :=by
   intro e K hK hr
   obtain ⟨a,ha,h⟩:=site_bound H e.letter w K hK hr
   refine Eq.mp (congr_arg _ (add_zero p)) ((Asympt.all hs K).op (q:=0) ha (by simpa using (Eventually.of_forall fun (y:E4) z hz=>h z hz (s y))))
lemma miss_site (H:S.Hierarchy) {s:E4→S.Field w} {g:FamilyData ℂ L}{p:ℝ}(he:AtPrice (fun e y z=>g e y z-siteValue S e.letter w (s y) 0 z) p): LocalBound (fun y=>pull w D g y - s y) p := by
  refine (pull_price w D he).congr (?_)
  refine Eventually.of_forall fun y i _=> ?_
  let v:=s y
  change D.decode (fun e => _ - _) = D.decode _ - _
  conv_rhs => enter [2]; rw [← D.fixes (s y)]
  rw [←map_sub]
  exact congr_arg D.decode (funext fun e=>by erw [site_orig S H.translations (e:Exterior L) w _ H.laws.toSymmetric (fun _=>le_rfl)]; rfl)

lemma detect (H:S.Hierarchy) {s:E4→S.Field w} {g:FamilyData ℂ L}{p:ℝ}(he:AtPrice (fun e y z=>g e y z-siteValue S e.letter w (s y) 0 z) p): AtPrice (fun e y z=>missAt w D g e z y) p := by
  have hc:= center_price w H.smooth (s:=fun y=>pull w D g y-s y) (miss_site w D H he)
  -- combine two inequalities
  intro e K hK hr
  refine ((he e K hK hr).sub (hc e K hK hr)).congr (Eventually.of_forall (fun y z _=>?_))
  change (_-_)-_=_
  unfold missAt siteValue fixedValue
  simp_rw [← Work.A01.front_eval,map_sub]; ring
end YM.MultipleContact.Two
