import YM.RG08.Calendar.Way
import YM.RG08.Curl.Moor
import YM.RG08.Fields.Surge
/-!
 # Width & age charges for vacuum + quad support
-/
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
noncomputable section
namespace YM.RG08.Admission
open Function Filter Lattice Wilson Exterior Precision Laurent Finset RG Next.Free RG.Supply Bloch Input Conductor Wings Stationary Staffer Drift Virtue
open scoped BigOperators Topology Real Classical
variable {I H:Type} {G:Gauge}{K:KernelChoices}

-- a combinator to use this as sub-obligation of e.g. Master exception grantor. pays ANY tail. combine costs before issuing options
structure Need.Higher (a b:Need):Prop where
  lift : b.pre≤ a.pre
  wind j i L v: b.cost j i L v ≤ a.cost j i L v
lemma Need.Higher.trans {a b c:Need}(h:a.Higher b)(he:b.Higher c): a.Higher c:=⟨he.lift.trans h.lift, fun j i L v=>(he.wind ..).trans (h.wind ..)⟩
lemma Affords.of_sub {w u:Need}{a:Levels G}{i:ℕ}(h:Affords w a i)(hp:w.Higher u): Affords u a i:= ⟨fun k hk=>(hp.lift _).trans (h.lo k hk),fun k hk=>(hp.wind ..).trans (h.hi k hk)⟩

def Need.brings (a b:Need): Need:=⟨a.pre⊔b.pre,fun j i L v=> max (a.cost j i L v) (b.cost j i L v)⟩
lemma Need.Higher.front (a b:Need): (a.brings b).Higher a:=⟨ le_sup_left,fun _ _ _ _=>le_max_left ..⟩
lemma Need.Higher.back (a b:Need): (a.brings b).Higher b:=⟨ le_sup_right,fun _ _ _ _=>le_max_right ..⟩
-- finite merging utility

def Need.basket [Fintype I] (a:I→Need) : Need:= ⟨fun i=> univ.sup (fun j=> (a j).pre i),fun j i L v=> ∑ k:I, |(a k).cost j i L v|⟩
lemma Need.Higher.wide [Fintype I] (a:I→Need)(k:I): (Need.basket a).Higher (a k):= ⟨fun i=> le_sup (s:=univ) (f:=fun k=> (a k).pre i) (mem_univ _),fun j i L v=> (le_abs_self _).trans (single_le_sum (s:=univ) (f:=fun k=> |(a k).cost j i L v|) (fun i _=>abs_nonneg _) (mem_univ _))⟩
lemma Need.basket_affords [Fintype I] (a:I→Need) {X:Levels G}{n:ℕ}(hx:Affords (Need.basket a) X n)(i:I): Affords (a i) X n:= hx.of_sub (Need.Higher.wide ..)

-- width itinerary for ALL single legs. chart ratio and color paint cost later.
structure Names (G:Gauge) (K:KernelChoices) where
   fund : KPrices K
   kGate: KGate fund
   cov : Lending G K
   bridge: Quilt K.penalty kGate.w
   act (e:ℕ) : Prism G K kGate cov e
   harbor (e d:ℕ) (p:G.ColorIndex) : Harbor (act e).η p d
lemma names (h:G.Simple)(κ:KernelChoices) : Nonempty (Names G κ):= by
   obtain ⟨P⟩:= k_prices κ; obtain ⟨g,hg⟩:= prepare P P.b P.positive (fun i=>le_rfl); obtain ⟨Q⟩:= lenders G κ
   obtain ⟨B⟩:= entrance κ.penalty_pos g.pos; let W:=fun e:ℕ=> Classical.choice (scheduled_prism G g Q e)
   exact ⟨⟨P,g,Q,B,W,fun e d i=> Classical.choice (harbors h i _ _ (W e).positive)⟩⟩

-- vacuum receipts; include inverse of every relevant width before block. Can use Z=1+log(2+log betaHat) even here despite comparisons later restored
section requisites
abbrev Voc (G:Gauge) := Fin 13
-- $ω even positivity
private lemma fundTor_nonneg (a b:ℝ)(G:Gauge)(X:Patch)(L:Repeated X.L)(k:KernelChoices): 0 ≤ fundsTor G a b X k L:= by
   unfold fundsTor; split
   next h=> exact (ears G a b h X k L).choose_spec.1
   exact zero_le_one

def voice_f (N:Names G K) {j i:ℕ}(f:Flight j i)(E:ℕ)(P:Voc G):ℝ:= ![((f.L.val:ℝ):ℝ), N.fund.bill i, N.cov.bill i f.patch, fundsTor G (N.fund.b i) (N.fund.bill i) f.patch K (Repeated.axisRule f.L f.odd), probeFee G ((N.act E).η i), N.bridge.C i, N.bridge.post j i f,N.bridge.fee i,(N.fund.b i)⁻¹,(N.kGate.w i)⁻¹,((N.act E).η i)⁻¹,(N.bridge.width i)⁻¹,(N.bridge.alpha j i)⁻¹] P
def voiceCard (N:Names G K)(E:ℕ)(p:Voc G):Need:= ⟨(N.act E).height, fun _ _ f _=> voice_f N f E p⟩
def prepPath (N:Names G K)(ν:G.ColorIndex)(E d:ℕ): Need:= ⟨fun _=>0, fun _ i _ _=> max ((N.harbor E d ν).charge i) ((N.harbor E d ν).height i)⁻¹⟩
private def prepG (G:Gauge)(D:ChartRatio G)(ν:G.ColorIndex)(K:KernelChoices)(j k:ℕ):Need:= ⟨fun _=>0,fun _ _ f _=> tariffTok ν f.patch D K j k⟩
def tintPath (N:Names G K)(D:ChartRatio G)(ν:G.ColorIndex)(E d:ℕ): Need:= (prepPath N ν E d).brings (Need.basket (fun p:(Fin (E+1)×Fin (E+3))=>prepG G D ν K p.1 p.2))
def fast (N:Names G K)(D:ChartRatio G)(E d:ℕ) : Need:= (Need.basket (voiceCard N E)).brings (Need.basket fun ν=>tintPath N D ν E d)
variable {a:Levels G}{N:Names G a.clock.kernel}{ν:G.ColorIndex}{D:ChartRatio G}{E d :ℕ}{u:I→Windows}
local notation "χ"=> Chain.actual a
structure Ball (N:Names G a.clock.kernel)(D:ChartRatio G)(ν:G.ColorIndex) (u:I→Windows) (E d:ℕ): Prop where
   yes : Circuit (X:=χ) (N.act E) ν D u
   plays: Plays (X:=χ) u N.bridge
   widthK : Weighed (Launch.farY (u:=u) χ) (fun i=>(N.fund.b (a.clock.J i.i))⁻¹)
   width_f : Weighed (Launch.farY (u:=u) χ) (fun i=>(N.kGate.w (a.clock.J i.i))⁻¹)
   width_v : Weighed (Launch.farY (u:=u) χ) (fun i=> ((N.act E).η (a.clock.J i.i))⁻¹)
   width_h : Weighed (Launch.farY (u:=u) χ) (fun i=>(N.bridge.width (a.clock.J i.i))⁻¹)
   width_a : Weighed (Launch.farY (u:=u) χ) (fun i=>(N.bridge.alpha (a.clock.J (i.i+1)) (a.clock.J i.i))⁻¹)
   width_path : Weighed (Launch.farY (u:=u) χ) (fun i=> ((N.harbor E d ν).height (a.clock.J i.i))⁻¹)
   costs_path : Weighed (Launch.farY (u:=u) χ) (fun i=> (N.harbor E d ν).charge (a.clock.J i.i))
lemma matters (hV:NearZ a u)(hp:G.Simple)(h:∀ i,5≤ a.clock.J (u i).start)(he:∀ i,Affords (fast N D E d) a (u i).start): Ball N D ν u E d:= by
   have hx i (p:Voc G): Affords (voiceCard N E p) a (u i).start:= Need.basket_affords _ ((he i).of_sub (Need.Higher.front ..)) _
   have hu i : Affords (tintPath N D ν E d) a (u i).start:= Need.basket_affords _ ((he i).of_sub (Need.Higher.back ..)) _
   let f i:= ((Chain.actual a).step (i:Launch u).i (.top _))
   have ht (p:Voc G)(he:∀ i, 0 ≤ voice_f N (f i) E p): Weighed (Launch.farY χ) (fun i:Launch u=> voice_f N (f i) E p):= Affords.cash_w hp hV (fun i=>hx i p) he (fun _=>le_rfl)
   have hP i:Affords (prepPath N ν E d) a (u i).start := (hu i).of_sub (Need.Higher.front ..)
   refine ⟨⟨?_,⟨Launch.you _,fun _=>min_le_right .., ht 0 (fun i=> Nat.cast_nonneg _),?_⟩,ht 1 (fun i=>N.fund.solvent _),ht 2 (fun i=>N.cov.solvent ..),ht 3 (fun i=>fundTor_nonneg ..),ht 4 (fun i=> probe_fee ..)⟩,⟨ht 5 (fun i=>N.bridge.solvent ..),ht 6 (fun i=> N.bridge.upright ..),ht 7 (fun i=> N.bridge.nonneg _)⟩,ht 8 (fun i=> inv_nonneg.mpr (N.fund.positive _).le),ht 9 (fun i=> inv_nonneg.mpr (N.kGate.pos _).le),ht 10 (fun i=> inv_nonneg.mpr ((N.act E).positive _).le),ht 11 (fun i=> inv_nonneg.mpr (N.bridge.wp _).le), ht 12 (fun i=>inv_nonneg.mpr (N.bridge.ap ..).le), Affords.cash_w hp hV hP (fun _=> inv_nonneg.mpr ((N.harbor E d ν).pos _).le) (fun _=>le_max_right ..),Affords.cash_w hp hV hP (fun _=> (N.harbor E d ν).toll _) (fun _=> le_max_left ..)⟩
   · intro i; exact ⟨(h i).trans (a.fits.mono (Nat.le_succ _)),(hx i 0).lo⟩
   intro j hj k hk; refine Affords.cash_w hp hV (fun i=> Need.basket_affords _ ((hu i).of_sub (Need.Higher.back ..)) (⟨j,by omega⟩,⟨k,by omega⟩)) ?_ (fun i=> le_rfl)
   intro i; exact (lump_sum ν _ _ _ zero_le_one).choose_spec.1
end requisites
end YM.RG08.Admission
