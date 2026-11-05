import YM.FullVolume.Artes.Sconce
/-! Per grade contraction in ℓ¹. Permit arbitrary Subcontrols via sold statements then compare. Match D3 with *arbitrary* D4 perturbation. -/
set_option autoImplicit false
noncomputable section
namespace YM.Stationary.Artes
open Function Filter Lattice RG Exterior Precision Wilson Bloch Laurent Matrix Finset Tree Supply
open Shade Beacon Flagship ConeRay Tralis WilsonStartup WilsonStartup.Change WilsonStartup.Change.Reading Next.Free Next.Free.Retort
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators Classical InnerProductSpace
variable {G: Gauge}{a:Levels G} {s:Sheet G}{L: Rolls s}{Q:PostCost L}{O:ChartRatio G}{m:ℕ}
variable {F H W: Tale a m}{J : FaceRow}{V:ℕ→ Reel G}
inductive Wish where | C | D | K
namespace Wish
def ar: Wish→ℕ
| C=> 2 | D=> 3|K=> 1
instance (p:Wish):NeZero p.ar:=by cases p <;> exact ⟨by decide⟩
def vow (R: Reel G)(p:Wish):Vow G p.ar:=match p with
| C=>R.e3|D=>R.e4|K=>R.e2
def reads (R: Flagship G)(p:Wish):Cameo G p.ar:=match p with
| C=>R.b|D=>R.c|K=>R.a
def loans (r t:ℝ)(p:Wish):=match p with
| C=> r|D=>r|K=>t
def tap (x:Wish)(a:Levels G)(m):= x.loans (a.params m).paths (a.clock.loopCap m)
def coins (x:Wish)(V:ℕ→ Reel G)(a:Levels G) (m)(C:Cameo G x.ar):= Beacon.fee ((vow (V m) x).δ) (a.params m).width C
def ord (p:Wish)(x y: Flagship G):Prop:=match p with
| C=>True|D=>x.b=y.b|K=>x.b=y.b ∧ x.c=y.c
def pour (x:Flagship G)(p:Wish)(y:Cameo G p.ar): Flagship G:=match p with
| C=> {x with b:= y}|D=>{x with c:=y}|K=> {x with a:=y}
lemma ordained (p:Wish)(x:Flagship G): p.ord x x:=by cases p; trivial; rfl; exact ⟨rfl,rfl⟩
@[simp] lemma at_pour (x:Flagship G)(p:Wish)(y): reads (pour x p y) p=y:=by cases p <;> rfl
lemma ord_pour (x:Flagship G)(p:Wish)(y:Cameo G p.ar): ord p x (pour x p y):=by cases p; trivial; rfl; exact ⟨rfl,rfl⟩
lemma ord_trans (p:Wish){x y z:Flagship G}(h:p.ord x y)(he:p.ord y z):p.ord x z:=by cases p; trivial; exact h.trans he; exact ⟨h.1.trans he.1,h.2.trans he.2⟩
lemma ord_symm (p:Wish){x y:Flagship G}(h:p.ord x y):p.ord y x:=by cases p; trivial; exact h.symm; exact ⟨h.1.symm,h.2.symm⟩
lemma C_birth (h:F.sold.b=H.sold.b):D.ord F.sold H.sold:=h
lemma brace (x:Wish){F:Flagship G}{p:ℕ→ Flagship G}{b B}(h:Flagship.Beacon p F b B):Gleam (fun i=> x.reads (p i)) (x.reads F) (x.loans b B):=by cases x; exact h.b; exact h.c; exact h.a
lemma traffic (x:Wish) (h:F.Earns Q O V J)(he:H.Earns Q O V J)(hw:W.Earns Q O V J)(a:G.ColorIndex)(hO:LocalRatio O)(u:ℝ)(h1:F.input.row=H.input.row)(h2:F.input.row=W.input.row)(h3:F.receipts.row=H.receipts.row)(h4:F.receipts.row=W.receipts.row)(hx:x.ord F.stock H.stock)(hp:x.ord F.stock W.stock)(hz: reads W.stock x=reads F.stock x+u • (reads H.stock x-reads F.stock x)): reads W.sold x= reads F.sold x+u • (reads H.sold x-reads F.sold x):=by
    cases x
    · exact Tale.swerves h he hw u h1 h2 h3 h4 hz
    · exact Tale.parade h he hw u h1 h2 h3 h4 hx hp hz
    exact (Tale.replay h he hw a hO u h1 h2 h3 h4 hx.1 hp.1 hx.2 hp.2 hz).2
lemma stellar (x:Wish){B t L:ℝ}{R:Reel G}{K:Flagship G}{P:PathData G}{p:Clip}(he: Lash R K P)(hp:P.Bounds p t B L): Beacon.fee ((vow R x).δ) t (reads K x) ≤ loans B L x:=by
    obtain ⟨hz,hA,hQ,hT⟩:= Flagship.grooves he hp; cases x; exact hQ.1.2.2; exact hT.1.2.2; exact hz.1.2.2
lemma vista (x:Wish){R:Reel G}{w:ℝ}(h:R.Price w): w<(x.vow R).δ:=by cases x; exact h.2.1; exact h.2.2; exact h.1
end Wish
-- Issue.IO. Frames
structure Counter (A:Levels G)(V: Horizon A) {O:ChartRatio G}(Q:PostCost L)(X: ℕ→Reel G) (P:MapPrices):Prop where
    daily:MailBox V Q X (Z:=O)
    staple: V.Suffices P
    oath N m : m ≤ N→ ∀ k, Bid.Sworn (V.H N m) (A.S.side m k) G
    helps: LocalRatio O
    nonterm: Nonempty G.ColorIndex
variable {X:MapPrices}{N:ℕ}(j:Horizon a)
-- Actual issuance.A row preserved
structure Alive (Q:PostCost L)(O:ChartRatio G) (j:Horizon a)(V:ℕ→Reel G)(T:Tale a m)(N:ℕ) :Prop where
   step:m<N
   stories:T.Earns Q O V (j.H N m).metric
   inside:T.input.row=rowPath (j.H N (m+1))
   paid : Bubble j Q O N m T.input T.receipts T.α T.Ψ

open Wish
private lemma fundsP {w d:ℝ}{i:ℕ}[NeZero i]{U:Cameo G i}{c}(h:w<d)(he:Beacon.fee d w U≤ c): SumBudget (fun i=> (ringT d U i).budget w) c :=
    let z:= permits h U; ⟨z.1,z.2.1,z.2.2.trans he⟩

def printZ (A: PlaqAxes →ℕ→ℝ × Slot)(V: Reel G)(x:Flagship G): PathData G:= ⟨A,ringT V.e2.δ x.a,ringT V.e3.δ x.b,ringT V.e4.δ x.c⟩

-- resource admissible Pad.Bank semantics
private lemma volume {P P':PathData G} {x:Flagship G}{J:Reel G}{p b c r} (h:P.Bounds p r b c)(hi:P.row=P'.row)(hf:Lash J x P')(hC:AtomWall (ringT J.e2.δ x.a) r c)(hX: AtomWall (ringT J.e3.δ x.b) r b)(hY: AtomWall (ringT J.e4.δ x.c) r b)(hx:Bs G (ringT J.e2.δ x.a)): P'.Bounds p r b c:=by
   rw [←hf.1] at hx hC; rw [←hf.2.1] at hX; rw [← hf.2.2] at hY
   refine ⟨h.width,?_,hC.1,hX.1,hY.1,fun i=>⟨hC.2 i,hX.2 i,hY.2 i⟩,?_,?_, fun i x=> ⟨(hx i x P' rfl).1.summable,fun l=> ((hx i x P' rfl).2 l).summable⟩,fun i x=> ⟨(hx i x P' rfl).1.tsum_eq,fun l=> ((hx i x P' rfl).2 l).tsum_eq⟩⟩
   · rw [←hi]; exact h.rows
   · rw [←hi]; exact h.symTerms
   have hp:= h.metric; unfold PathData.metric_zero PathData.symbol0 at *; rw [←hi]; exact hp
-- splice in a capsule.Buy.Back bone.
lemma bond (x:Wish)(S T:Flagship G){R P Q:PathData G}{p v A B}{V:Reel G}(h: Lash V S R)(hp:R.Bounds p v A B)(ht:Lash V T P)(hb:P.Bounds p v A B)(he:Lash V (x.pour S (x.reads T)) Q)(hr:R.row=Q.row) : Q.Bounds p v A B:=by
   obtain ⟨h1,b1,e1,g1⟩:=grooves h hp; obtain ⟨h2,b2,e2,g2⟩:=grooves ht hb; cases x
   · exact volume hp hr he h1 e2 g1 b1
   · exact volume hp hr he h1 e1 g2 b1
   exact volume hp hr he h2 e1 g1 b2
lemma advance (x:Wish)(S T:Flagship G)(u:ℝ){w p b d}{R P Q:PathData G}{V:Reel G}(hV:V.Price w)(he: Lash V S R)(he':R.Bounds p w b d)(hP:Lash V T P)(hu:P.Bounds p w b d) :
     let C:= x.reads S + u • (x.reads T-x.reads S)
     Beacon.fee (x.vow V|>.δ) w C≤ x.loans b d→ Q.row=R.row→ Lash V (x.pour S C) Q→ Q.Bounds p w b d:=by
     cases x <;> intro z hc hQ hh <;> obtain ⟨h1,b1,e1,g1⟩:=grooves he he' <;> obtain ⟨h2,b2,e2,g2⟩:=grooves hP hu
     · refine volume he' hQ.symm hh h1 ⟨fundsP (hV.2.1) hc,?_⟩ g1 b1
       let W:=core G 2 _ V.e3.hired; -- ambiguous
       have hv:S.b∈W.s:= (gold V.e3.hired S.b).2 e1.2
       exact (gold V.e3.hired z).1 (W.s.add_mem hv (W.s.smul_mem u (W.s.sub_mem ((gold V.e3.hired _).2 e2.2) hv)))
     · refine volume he' hQ.symm hh h1 e1 ⟨fundsP hV.2.2 hc,?_⟩ b1
       let W:=core G 3 _ V.e4.hired
       have hv:S.c∈W.s:= (gold V.e4.hired S.c).2 g1.2
       exact (gold V.e4.hired z).1 (W.s.add_mem hv (W.s.smul_mem u (W.s.sub_mem ((gold V.e4.hired _).2 g2.2) hv)))
     let W:=Shade.cut G _ V.e2.hired
     have hv:S.a∈W.s:= (silver V.e2.hired S.a).2 ⟨b1,h1.2⟩
     have ht:= (silver V.e2.hired z).1 (W.s.add_mem hv (W.s.smul_mem u (W.s.sub_mem ((silver V.e2.hired _).2 ⟨b2,h2.2⟩) hv)))
     exact volume he' hQ.symm hh ⟨fundsP hV.1 hc,ht.2⟩ e1 g1 ht.1
variable {j} (h:Counter a j (O:=O) Q V X)
namespace Alive
include h
lemma destiny {m N:ℕ}(R:PathData G)(he:m<N)(hx: R.row=rowPath (j.H N (m+1)))(z:Flagship G)(ht: Lash (V (m+1)) z R)(hv:haloB a (m+1) R):∃ T:Tale a m,T.input=R ∧ T.stock=z ∧ Alive Q O j V T N:=by
     obtain ⟨F,α,Ψ,hp,hF⟩:= h.daily.resumes m N he R hv (rows_layout hx)
     obtain ⟨t,H,hT⟩:=laying hF; let S:Tale a m:=⟨R,z,F,t,Ψ,α⟩
     exact ⟨S,rfl,rfl,he,Tale.fromE (T:=S) hp h.staple (h.oath _ _ he.le) he ht H hT hv,hx,hp⟩
def feeB (a:Levels G)(i:ℕ)(T:PathData G):= T.Bounds (a.params i).clip (a.params i).width (a.params i).paths (a.clock.loopCap i)
lemma lawful (x:Wish)(m):0<x.tap a m:=by cases x <;> first|exact (a.params m).paths_pos| exact one_pos.trans_le (h.daily.step _)
lemma afford (x:Wish)(hf: Alive Q O j V F N)(hp: feeB a (m+1) F.input): x.coins V a (m+1) (x.reads F.stock) ≤ x.tap a (m+1):= x.stellar hf.stories.arrives hp
lemma claim (x:Wish)(hf: Alive Q O j V F N): x.coins V a m (x.reads F.sold) ≤ x.tap a m:= x.stellar hf.stories.goes hf.stories.out
lemma snips (x:Wish)(hf: Alive Q O j V F N)(hH: Alive Q O j V H N) (hp:feeB a (m+1) F.input)(ht:feeB a (m+1) H.input)(hy:x.ord F.stock H.stock):
     x.coins V a m (x.reads H.sold-x.reads F.sold) / x.tap a m ≤ (1/4:ℝ) * (x.coins V a (m+1) (x.reads H.stock-x.reads F.stock) / x.tap a (m+1)):=by
   obtain ⟨i⟩:=h.nonterm
   let S:=x.tap a m; let S':=x.tap a (m+1); have hs :0<S:=lawful h x m; have hs' :0<S':=lawful h x _
   let z:= x.coins V a (m+1) (x.reads H.stock - x.reads F.stock); have hI:=x.vista (h.daily.vista (m+1)); have hd:= x.vista (h.daily.vista m)
   have hZ : 0 ≤ z:= cover_at hI _; have hA:=hf.inside.trans hH.inside.symm; have hB:= hf.paid.lives.row.trans hH.paid.lives.row.symm
   rcases eq_or_lt_of_le hZ with he | he
   · have hE := (sub_eq_zero.mp (money hI he.symm));
     have hx:x.reads H.sold=x.reads F.sold:=by
          have ht:=traffic x hf.stories hf.stories hH.stories i h.helps 0 rfl hA rfl hB (x.ordained _) hy (by rw [hE]; simp)
          simpa using ht
     have h: x.coins V a m 0=0:=by
         unfold Wish.coins; simpa using (everybody (C:= (0:Cameo G x.ar)) hd 0)
     rw [hx,sub_self,h]; change _ ≤ 1/4*(z/S'); rw [← he]; simp
   let W:= (V (m+1)); let y:= H.stock; let d:=F.stock; let L:=32*S'/z; let C:=x.reads d+L • (x.reads y-x.reads d); let D:= x.pour d C; let X0:= printZ F.input.row W D
   have hL: 0<L:= by unfold L; positivity
   have hz: x.coins V a (m+1) C≤64*S':=by
      unfold Wish.coins C; apply (Beacon.charge hI ..).trans; rw [everybody hI, abs_of_pos hL];
      have hh : L*z=32*S':=div_mul_cancel₀ _ he.ne'
      have ht:x.coins V a (m+1) (x.reads d) ≤ S':= afford h x hf hp
      change _+ L*z ≤ _; unfold Wish.coins at ht; linarith
   have hr: Lash W D X0 := ⟨rfl,rfl,rfl⟩; have hu:haloB a (m+1) X0 :=by
         refine advance x d y L (R:=F.input) (P:=H.input) (h.daily.vista (m+1)) hf.stories.arrives hf.stories.bounds hH.stories.arrives hH.stories.bounds (?_) rfl hr
         apply hz.trans; change 64*x.tap a (m+1) ≤ _; cases x <;> dsimp [Wish.tap,Wish.loans] <;> first|exact le_rfl|ring_nf; all_goals exact le_rfl
   obtain ⟨P,hh,hv,hX⟩:= destiny h X0 hf.step (show X0.row= _ from hf.inside) D hr hu
   have he':x.reads P.stock=C:=by rw [hv]; exact Wish.at_pour ..
   have hh':= traffic x hf.stories hH.stories hX.stories i h.helps L hA (by rw [hf.inside,hX.inside]) hB (by rw [hf.paid.lives.row,hX.paid.lives.row]) hy (by rw [hv]; exact ord_pour .. ) he'
   let Z:= x.coins V a m (x.reads H.sold - x.reads F.sold)
   have hb : L*Z ≤ 2*S:=by
       calc
        _ = x.coins V a m (x.reads P.sold - x.reads F.sold):=by rw [hh',add_sub_cancel_left]; unfold Z Wish.coins; rw [everybody hd,abs_of_pos hL]
        _ ≤ x.coins V a m (x.reads P.sold)+ x.coins V a m (x.reads F.sold):= grime hd ..
        _ ≤ _:=by rw [two_mul]; exact add_le_add (claim h x hX) (claim h x hf)
   change Z/S ≤ 1/4 * (z/S'); rw [←mul_div_assoc,div_le_div_iff₀ hs hs'] -- calc
   unfold L at hb; rw [div_mul_eq_mul_div,div_le_iff₀ he] at hb; nlinarith only [hb,hs,he]
end Alive
end YM.Stationary.Artes
