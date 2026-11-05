import YM.UVExtension.Wet.Laces
import YM.UVExtension.Wet.Heron
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Blush.Wind
import YM.UVExtension.Wet.Tunes
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Wet
open Function Filter Set Lattice RG Pressure Pressure.Tube Tree Wilson Finset MeasureTheory
open ConnectedActivityE6 Shell Coat SliceRows Pulse Mask Raw Matter Pond PhysicalNext.Repeat
open Push Push.AbsoluteSums Gas Ursell Trees Multiple Letter OmitClusters RG Shoot Precision SectorMeasure Oriented
open AnalyticBridge VerifiedReset Collection Quotes UVNext Next.Scheduling
open Extra.Iteration Greenbelt Match Song Refrain
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Height Brim Time Supply Daisy Charity Lotus Blush Mallow
open Progress.DirectedRecipe Concert Span Wren Gala Badge Steady Next.Foundations
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G: Gauge}{d:ℕ}{ι κ:Type}{v:Filter ι}{n:Side}
lemma darts {c f : Side}{S: StepData c f}(u v:Molecule S→Support c)(h:u=v)(j:Clusters (Cold u))[Countable (Clusters (Cold u))][Countable (Clusters (Cold v))] : @Encodable.encode (Clusters (Cold u)) (Classical.choice (nonempty_encodable _)) j= @Encodable.encode (Clusters (Cold v)) (Classical.choice (nonempty_encodable _)) (grass u v h j):=by subst v; rw [grass_self]
lemma lofty {E: κ→Type}{f:ι→(x:κ)→E x→ℝ}(h:Transit v f): Transit v (fun n i x=> ((f n i x:ℝ):ℂ)):=by obtain ⟨q,hq,hH⟩:=h.rain; exact ⟨⟨_,hq,hH.mono (fun i hh j x=> (Complex.norm_real _).trans_le (hh j x))⟩,fun i=> (h.meters i).cont Complex.continuous_ofReal⟩
lemma petals {E:κ→Type}{f:ι→(x:κ)→E x→ℂ}(h:Transit v f)(c:ℂ): Transit v (fun n i x=> c*f n i x):=by obtain ⟨q,hq,hH⟩:=h.rain; refine ⟨⟨_,hq.scales _ (norm_nonneg c),hH.mono fun i hp j x=>?_⟩,fun i=> (h.meters _).cont (continuous_const.mul continuous_id)⟩; rw [norm_mul];exact mul_le_mul_of_nonneg_left (hp j x) (norm_nonneg c)
-- Name.Score.Span support.Content.NET proof.
lemma expansive {q :κ↪ℕ}{U:ℕ→Type}{Q:ι→(i:ℕ)→U i→ℂ}(h:Transit v (fun n i u=> Q n (q i) u))(hz:∀ i n,i∉ Set.range q→Q n i=0):Transit v Q:=by
   -- copy expand
   obtain ⟨f,hf,hq⟩:=h.rain
   let g n:=Function.extend q (f n) 0; have hm n k:g n (q k)= f n k:=q.injective.extend_apply ..; have hs(n i)(h:i∉ Set.range q):g n i=0:=extend_apply' _ _ _ h
   have hp:Swift v g:=by
       obtain ⟨K,hK⟩:= hf.books; constructor
       · refine ⟨K,hK.mono fun n hn=>?_⟩; apply Local.sumBudget_pass q _ ?_ (hs n); simp_rw [hm]; exact hn
       intro ε he; obtain ⟨s,hs'⟩:= hf.drops ε he; refine ⟨s.map q,hs'.mono fun n hn=> ?_⟩; apply Local.sumBudget_pass q _ _ _
       · simp_rw [hm,Finset.mem_map]; simp only [EmbeddingLike.apply_eq_iff_eq,exists_eq_right]; convert! hn using 2 with i
       intro i hi; split; rfl; exact hs _ _ hi
   refine ⟨⟨g,hp,hq.mono (fun n hn i k=>?_)⟩,fun i=> ?_⟩
   · by_cases he:i∈ Set.range q; obtain ⟨j,rfl⟩:=he; rw [hm]; exact hn j k
     rw [hs n i he,hz i n he,Pi.zero_apply,norm_zero]
   by_cases he:i∈ Set.range q; obtain ⟨j,rfl⟩:=he; exact h.meters j
   simp_rw [fun n=>hz i n he,Pi.zero_apply]; exact Tune.nil
variable {c f L:Side} {W x μ C a:ℝ} {S:StepData c f}{T:ι→ Tube G S}{I: Teller G} {Q: ConnectedActivityE6.Target G I}{o':Target.Order G W}{R:ι→RG.Rep G f}
variable [NeBot v] [v.IsCountablyGenerated]{P:BudgetPoint} {H:∀ i,Cash W x μ L Q o' C (T i) (R i)}(p:Choir v T H P.order Chi.canonical)(h:StableR v R)
    (r :(i:ι)→ Cloud (R i))(j:ι)(hD: Constant (v:=v) (fun i=>(r i).live))(hC:Constant (v:=v) (fun i=>(r i).pale))(hp: P.threshold=temp x)(hs:Cooling (H:=H) (χ:=Chi.canonical) (k:=P.order) P a)(hy:∀ i, (0:Site c)∈ (r i).live.crest.image S.ratio.parent)
local notation "o"=> (0:Site c)
local notation "X"=> Blush.scope (H j) (r j) (0:Site c)
set_option quotPrecheck false
local notation "J"=> (H j).fragrances
include p h
lemma datum (v: (H j).fragrances)(n) : Blush.enter (H j) v= Blush.enter (H n) (p.casts h j n v):= darts _ _ (p.stirs h j n) _ -- universes countable
lemma zonesR (i:ℕ)(he:i∉Set.range (Blush.enter (H j)))(n): i ∉ Set.range (Blush.enter (H n)):= by rintro ⟨j',rfl⟩; obtain ⟨s,rfl⟩:= (p.casts h j n).surjective j'; exact he ⟨_,datum p h j _ _⟩
include hD
lemma scenes (n): scope (H n) (r n) o=X:=by
   funext i; unfold scope; by_cases he:i∈Set.range (Blush.enter (H j))
   swap; · rw [extend_apply' _ _ _ he,extend_apply' _ _ _ (zonesR p h j _ he n)]
   obtain ⟨i,rfl⟩:=he; rw [(Blush.enter (H j)).injective.extend_apply,datum p h j i n,(Blush.enter (H n)).injective.extend_apply]; exact heights p h hD j o i n
include hp hs hy hC
lemma panelsC (v':ℂ) : Cof (v:=v) P X (fun i=>fields (H i) (r i) v') :=by
   let f n:=fields (H n) (r n) v'; have hg(i):o∈ (r i).pale.crest.image S.ratio.parent := ((r i).turnout ▸ hy i)
   let Y m := locus (r j).live (H j) o m
   have hx m: X (Blush.enter (H j) m)=Y m:=(Blush.enter (H j)).injective.extend_apply ..
   let g n m:= froth p h j (fun i=>(r i).live) m n; let k n m:= froth p h j (fun i=>(r i).pale) m n
   have hk:∀ i n,f i (Blush.enter (H j) n)=v' • ((Complex.ofReal ∘ g i n) + Complex.I • (Complex.ofReal ∘ k i n)):=by
      intro i n; unfold f fields; rw [datum p h j n i,stuffed]; rfl
   have hv:=choirC p h hD j P rfl hp hs o hy
   have hu:Notes v P (fun i=>(⟨o,Y i,seatY (r j).live (H j) o (hy j) i⟩: RegularAddress c)) (fun n x=> k n x):=by
      let E i:RegularAddress c:=⟨o,locus (r j).pale (H j) o i,seatY _ _ o (hg j) i⟩; have ht : Notes v P E (fun n x=> k n x):= choirC p h hC j P rfl hp hs o hg
      have he:E=(fun i =>(⟨o,Y i,seatY (r j).live (H j) o (hy j) i⟩: RegularAddress c)):=funext fun i=>reg_ext rfl (Blush.arches (H j) (r j) o i).symm
      exact he ▸ ht
   let q n m:= Complex.ofReal ∘ g n m; let V n m:= Complex.ofReal ∘ k n m; let d' n m:= (v' • (q n m+Complex.I • V n m))
   have hQ n m:P.Regular (Y m) (q n m):= ornate (hv.available n m); have hV n m:P.Regular (Y m) (V n m):= ornate (hu.available n m); have he n m:= regular_add (hQ n m) (regular_smul Complex.I (hV n m))
   have hJ i n (hz:i∉Set.range (Blush.enter (H j))): f n i=0:= Progress.DirectedRecipe.blank _ _ (zonesR p h j i hz n)
   have hN : Transit v (fun n i (V: Tap P G 0 (Y i))=>V.read (d' n i)):=by
       have hs:= petals ((lofty hv.invests).together (petals (lofty hu.invests) Complex.I)) v'
       let fB (m) (v: Tap P G 0 (Y m))(g:Config G c→ℝ)(h:P.Regular (Y m) g):v.read (Complex.ofReal ∘ g)=(v.read g:ℝ):= Local.left_linear Complex.ofRealCLM v.poll (h.smooth _ v.live) v.card -- coe mixed
       have hW(m) (v: Tap P G 0 (Y m))(g:Config G c→ℂ)(h:P.Regular (Y m) g)(c:ℂ):v.read (c • g)=c*v.read g:=Local.left_linear (c • ContinuousLinearMap.id ℝ ℂ) v.poll (h.smooth _ v.live) v.card
       apply hs.fade; filter_upwards with i m; funext x; unfold d'; rw [hW m x _ (he ..),show x.read (q i m+Complex.I • (V i m))=x.read (q i m)+x.read (Complex.I • (V i m)) from Local.left_add x.poll ((hQ i m).smooth _ x.live) ((regular_smul _ (hV i m)).smooth _ x.live) x.card,hW m x _ (hV ..),show x.read (q i m)= _ from (fB m x (g i m) (hv.available ..)), show x.read (V i m)=_ from (fB m x (k i m) (hu.available ..))]
   change Cof (v:=v) P X f
   refine ⟨fun i m=>?_, expansive (q:=Blush.enter (H j)) ?_ ?_⟩
   · by_cases hu:m∈ Set.range (Blush.enter (H j)); obtain ⟨m,rfl⟩:= hu; rw [hk,hx]; exact regular_smul _ (he ..)
     rw [hJ m i hu]; exact (Eyelet.hot («o»:=o) _ _).1
   · simp_rw [show ∀ i m,f i (Blush.enter (H j) m)= d' i m from hk]; -- need dependent equality program function.Lens general lemma
     have hp: ∀ m, (X ∘ Blush.enter (H j)) m=Y m:=hx; let I:= X ∘ (Blush.enter (H j)); have hh :Transit v (fun n m (u:Tap P G 0 (I m))=> u.read (d' n m)):= by rw [show I=Y from funext hp]; exact hN
     exact hh
   intro i n hv; funext v; rw [hJ _ _ hv]; simp only [Tap.read]; rw [show (0:Config G c→ℂ)=fun _=>0 from rfl,Work.G07.left_const,ite_self]; rfl
end YM.UVExtension.Wet
