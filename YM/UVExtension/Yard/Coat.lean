import YM.UVExtension.Yard.Graft
import YM.UVExtension.Lamppost.Promote
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Yard
open Function Filter Set RG Wilson Lattice Precision Push Push.AbsoluteSums Finset
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration WilsonStartup Residual Averaging Geo
open Lamppost Concert
open scoped Topology BigOperators ContDiff Classical Matrix.Norms.Frobenius
variable {G : Gauge} {n : Side} {p : BudgetPoint} {P : Listing G n} {X:Support n} {D Y : Type}
    [NormedAddCommGroup Y] [NormedSpace ℂ Y] {M:Opening D Y} {σ C Λ b c : ℝ}
    (a:D→ Collection.Source G n)
    (K : PathData G)(v:Clip)
variable (hG : G.Simple) (F:Atlas (fork p G P.reg (preExponent p)) M (fun d=>trill p G P.reg (preExponent p) (a d).logRead) (fun _=>b))
    (H:∀ d,smoothP p P.reg (a d).logRead)

variable {A:Collection.Source G n}
    (hv:Decent v p)(hK: K.Bounds v σ C Λ)(he: Geo.Width p v σ)
variable {X:Ovens.Pipes G n}(V:D→ Ovens.Tap G n)
open Progress.DirectedRecipe Rack Ovens.Pipes
def priceE (b x σ C:ℝ)(v:Clip)(p:BudgetPoint)(G:Gauge):= regularNeed G p v σ C x 0+4*regularNeed G p v σ C 0 1*b
def priceS (b x σ C:ℝ)(v:Clip)(p:BudgetPoint)(G:Gauge):= softNeed G p v σ C x 0+4*softNeed G p v σ C 0 1*b
include hv hK he hG H F
lemma full (x:ℝ)(hb:0 ≤ b): let X:= shelves P K p; let V i:= branch P K v p (a i) x
    (∀ i,smoothP p X.reg (V i).regular) ∧ Nonempty (ticketR M p X.reg p.supportExponent (fun i=> (V i).regular) (fun _=>priceE b x σ C v p G)) ∧ Nonempty (Atlas (softer X p.B (p.supportExponent+1)) M (fun i j u=> (V i).logarithm j u) (fun _=>priceS b x σ C v p G)):=by
  intro X V
  let Y i:= branch P K v p (a i) 0; let Z:= branch P K v p (vacant G n) x; let p' := fork p G X.reg p.supportExponent
  have h i: smoothP p X.reg (V i).regular:= (switch K v hG hv hK he x (H i) (truth a F i)).1; refine ⟨h,?_⟩
  have hc:= switch K v hG hv hK he x (vacant_norm (P:=P) (p:=p)) vacant_cost
  obtain ⟨⟨G₁⟩,⟨G₂⟩⟩:= evens P a K v hG F H hv hK he hb
  obtain ⟨K₁⟩:= Lamppost.lit (M:=M) _ _ _ hc.2.1; obtain ⟨K₂⟩:= Lamppost.lit (M:=M) _ _ _ hc.2.2
  obtain ⟨G'⟩:= Lamppost.both _ _ _ K₁ G₁; obtain ⟨K'⟩:= Lamppost.both _ _ _ K₂ G₂
  have hp(i:D):= proud K v (P:=P) (p:=p) x (a i)
  let g i:= trill p G X.reg p.supportExponent (V i).regular
  constructor
  · change Nonempty (Atlas p' M g _); rw [show g=_ from ?_]; exact ⟨G'⟩
    funext i k H'; let u: Concert.Tap p G (X.reg k).site (X.reg k).support:= H'
    change u.read ((V i).regular k)=trill p G X.reg p.supportExponent Z.regular k u +u.read ((Y i).regular k)
    have hv:=Push.Local.left_add u.poll (show Push.Local.Chart p.order (Z.regular k) u.view from (hc.1 k).smooth u.view u.live) (show Push.Local.Chart p.order ((Y i).regular k) u.view from ((switch K v hG hv hK he 0 (H i) (truth a F i)).1 k).smooth u.view u.live) u.card
    rw [(show (V i).regular _= _ from (hp i).1 k)]; exact hv
  let J':= softer X p.B (p.supportExponent+1); let v i:J'.Slot:= fun j u=> (V i).logarithm j u; change Nonempty (Atlas J' M v _); rw [show v= _ from ?_]; exact ⟨K'⟩
  funext i j d; exact (hp i).2 j d
omit hv hK he hG H F
private def regW {A' B:RegularAddress n} (h:A'=B) (x:Concert.Tap p G A'.site A'.support): Concert.Tap p G B.site B.support:= h ▸ x
private lemma regUse {A' B:RegularAddress n} (h:A'=B)(x:Concert.Tap p G A'.site A'.support)(f:Config G n→ℝ): x.read f=(regW h x).read f := by subst B; rfl

lemma spanE (F:ticketR M p X.reg p.supportExponent (fun i=>(V i).regular) (fun _=> b)) (h:∀ i,smoothP p X.reg (V i).regular) :
    (∀ i,smoothP p (drawer G n).reg ((widen X (V i)).regular)) ∧Nonempty (ticketR M p (drawer G n).reg p.supportExponent (fun i=> (widen X (V i)).regular) (fun _=> b)) :=by
  let f := fun i=> (widen X (V i)).regular
  have hr i j: f i (upE X j)=(V i).regular j:= stuffed ..
  have he i j (hj: j∉ Set.range (upE X)): f i j=0:= blank _ _ hj
  refine ⟨fun i j=>?_,?_⟩
  · by_cases hx: j∈range (upE X)
    · obtain ⟨j,rfl⟩:=hx; change p.Regular _ (f i _); rw [reg_up,show _=_ from hr i j]; exact h i j
    change p.Regular _ (f i j); rw [he i j hx]; exact CouplingShape.reg_const _
  apply Lamppost.inserted _ _ _ (upE X) _ (fun i k=> regW (reg_up X i) k) _ _ _ F
  · intro i j k
    let H:= show Concert.Tap p G _ _ from k; change H.read (f i (upE X j))=_; rw [hr]; exact regUse _ H _
  · intro i hi j k
    let H := show Concert.Tap p G _ _ from k; change H.read (f j i)=0; rw [he j i hi]; unfold Concert.Tap.read; rw [show leftDerivs (0 : Config G n→ℝ) H.poll H.view=_ from Work.G07.left_const 0 _ _]; split<;>rfl
  intro i j; dsimp only [fork]; rw [reg_up]

lemma spansH (F:Atlas (bell X.kernel p.B (p.supportExponent+1)) M (fun i j u=> (V i).forced j u) (fun _=> b)) : Nonempty (Atlas (bell (drawer G n).kernel p.B (p.supportExponent+1)) M (fun i j u=> (widen X (V i)).forced j u) (fun _=>b)):= by
  refine Lamppost.inserted _ _ _ (upK X) _ (fun i=>id) (fun d i k=> congr_fun (show (widen X (V d)).forced (upK X i)=_ from stuffed ..) k) (fun i hi d k=> congr_fun (show (widen X (V d)).forced i=0 from blank _ _ hi) k) ?_ F
  intro i j; dsimp only [bell]; rw [hard_up]; rfl
lemma spansS (F:Atlas (softer X p.B (p.supportExponent+1)) M (fun i j u=> (V i).logarithm j u) (fun _=> b)) : Nonempty (Atlas (softer (drawer G n) p.B (p.supportExponent+1)) M (fun i j u=> (widen X (V i)).logarithm j u) (fun _=>b)):= by
  refine Lamppost.inserted _ _ _ (upS X) _ (fun _=>id) (fun d i k=> congr_fun (show (widen X (V d)).logarithm (upS X i)=_ from stuffed ..) k) (fun i hi d k=> congr_fun (show (widen X (V d)).logarithm i=0 from blank _ _ hi) k) ?_ F
  intro i j; dsimp only [Concert.softer]; rw [soft_up]

open Progress.DirectedRecipe
include hG hv hK he H F
lemma result {g w u s k:ℝ}(P':Atlas (bell P.hard p.B (p.supportExponent+1)) M (fun i j u=> (a i).hardRead j u) (fun _=>c))(hg:0≤ b)(hc:priceE b g σ C v p G≤ u) (hp:priceS b g σ C v p G ≤ s) (hr:Payments.Rates p.B w c s k): let X:= shelves P K p; let V i:=(finish K v p X (branch P K v p (a i) g) 0 0).activities
    (∀ i,smoothP p (drawer G n).reg (V i).E)∧Nonempty (ticketR M p (drawer G n).reg p.supportExponent (fun i=> (V i).E) (fun _=> u)) ∧ Nonempty (Atlas (bell (addr (folio G n) p) p.B p.supportExponent) M (fun i j u=> (V i).K j u) (fun _=>w)):=by
  intro X V
  obtain ⟨h,⟨hP⟩,⟨hF⟩⟩:= full a K v hG F H hv hK he g hg; let G i:= branch P K v p (a i) g
  obtain ⟨hh,⟨hq⟩⟩:= spanE G hP h
  obtain ⟨G₁⟩:= spansH (p:=p) (X:=X) G P'; obtain ⟨G₂⟩:= spansS (p:=p) G hF; obtain ⟨hr'⟩:= Lamppost.raiseCredit _ _ G₂ (g:=fun _=>s) (fun _ _=> hp)
  exact ⟨hh,Lamppost.raiseCredit _ _ hq (fun _ _=> hc),Concert.brittle _ (folio _ _) G₁ hr' hr⟩
end YM.UVExtension.Yard
