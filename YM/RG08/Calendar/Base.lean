import YM.RG08.Crossing.Coin
import YM.Push.PRICE_COMPILER.Post
/-!
 # Admitted wing setup

 All RG statements remain parametric in prescribed data. Here a
 calendar-building add-on, e.g. so a PhysicalContext integrator doesn't
 have to postulate a Fits having these additional properties. Does NOT
 assert other demands for proving REAL estimates can be announced in
 this or the base format. Buying with finite lists per stage, may add
 arbitrary more from these scopes. `z` buying log log hatBeta
 costs (use log(2+log x) for x>1).

 Orders in the Working statements to come have no implication for
 constants as test order tends to infinity on a fixed level. We adopt
 the *admitted tail per fixed-demand* convention of kbulk. This will be
 a countable table of pre-block strip and gain purchases and real charges
 for formal data. Not changing bases/horizon per reporting cutoff to
 make the table fit.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG08.Admission
open Set Function Filter Lattice Wilson Exterior Precision Laurent FreeResolvent Profiles Next.Free RG RG.Supply Bloch Input
open Push.PriceCompiler
open scoped BigOperators Topology Real Classical
variable {I H:Type} {G:Gauge}

-- Single request over stages; costs can use predecessor j too and
-- its Stage bill. Evaluated on the NOVEL a (Flight with top -- trivial
-- wing, not the loaded one from the actual recursion). Thus post-block,
-- no history dependence. May pay for WIDTHS already chosen before block.
structure Need where
  pre : ℕ→ℕ
  cost : (j i:ℕ) → Flight j i → RG.Stage → ℝ

def LambdaX (v:ℝ) := 2+Real.log v
def zview (v:ℝ) : ℝ:=1+Real.log (LambdaX v)
abbrev z (a:Levels G)(i:ℕ):= zview (a.clock.hatBeta i)
lemma z_rises : Tendsto zview atTop atTop := by
  apply tendsto_atTop_add_const_left
  exact Real.tendsto_log_atTop.comp (tendsto_atTop_add_const_left _ _ Real.tendsto_log_atTop)
structure Affords (w:Need)(a:Levels G)(i: ℕ) : Prop where
   lo m: i≤ m → w.pre (a.clock.J (m+1)) ≤ (a.S.block m).val
   hi m: i≤ m → w.cost (a.clock.J (m+1)) (a.clock.J m) ((Chain.actual a).step m (.top _)) (a.clock.params m) ≤ z a m
-- consumer can also impose the entrance index-length/cut convention independent of Field heights. Raising admission preserves costs
lemma Affords.later {w:Need}{a:Levels G}{i j:ℕ}(h:Affords w a i)(p:i≤j): Affords w a j:=⟨fun m hi=>h.lo m (p.trans hi),fun m hi=>h.hi m (p.trans hi)⟩

section buy
variable [Encodable I] (w:I→Need)
open Finset Encodable
-- arbitrary increases before Rolls supported
private lemma coded : ∃ f:ℕ→ℕ, ∀ v:I, ∀ j, Encodable.encode v≤ j → (w v).pre j ≤ f j:=by
   let B i j := ((decode (α:=I) i).map w).map (fun W=>W.pre j)|>.getD 0
   refine ⟨fun j=>(range (j+1)).sup (fun i=> B i j),fun i j hi=>?_⟩
   exact (show _= B (encode i) j by simp [B]).trans_le (le_sup (s:=range _) (f:=fun i=> B i j) (mem_range.mpr (by omega)))
def prePay : ℕ→ℕ:= (coded w).choose

private def postPay (L:Side)(X:Need)(j i:ℕ)(v:RG.Stage):ℝ:= if h:Odd L.val ∧ 3≤L.val∧4≤j∧i ≤ j∧ j ≤ i+1 then X.cost j i ⟨L,h.1,h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2,.top j⟩ v else 0
variable {s:Sheet G} {P:Rolls s}{θ:Protection P}
private lemma postAccepted (L:Rolls s)(i:ℕ) : ∀ᶠ x : ℝ in atTop, (∀ k : I,encode k ≤ i → ∀ j : ℕ, j ≤ i → postPay (L.L i) (w k) i j (s.profile j) ≤ zview x):=by
   let F:=fun k j=> ((decode (α:=I) k).map w).map (fun X=>postPay (L.L i) X i j (s.profile j))|>.getD 0
   have he: ∀ᶠ x in atTop,∀ (a b:Fin (i+1)), F a b ≤ zview x := eventually_all.mpr fun a=>eventually_all.mpr fun b=> z_rises.eventually (eventually_ge_atTop _)
   filter_upwards [he] with x hx k hu j hj
   simpa only [F,encodek,Option.map_some,Option.getD_some] using hx ⟨_,show encode k< i+1 by omega⟩ ⟨_,show j< i+1 by omega⟩
-- buys on EVERY later version of D and Paid W. robust to raising
-- once other computations finished. No bar limit along stage demanded.
theorem minDelay (h:∀ i,prePay w i ≤ (P.L i).val) (T:Delays θ) : ∃ V:Delays θ,DelayLe T V∧
   ∀ (Z:Delays θ)(Y:Bar Z)(W:Wait Y) (a:Levels G),DelayLe V Z → Paid W a→∀ k:I,∀ n,encode k ≤ a.clock.J n → Affords (w k) a n:= by
   obtain ⟨V,hV,-,Hv⟩:= delay_extra T (fun j x=> ∀ o:I,encode o ≤ j→∀ l,l≤j→postPay (P.L j) (w o) j l (s.profile l)≤ zview x) (fun _ _ _=> True) (postAccepted w P) (fun _ _=>Eventually.of_forall fun _ => True.intro)
   refine ⟨V,hV,fun Z Y W a hh hx k n hN=>?_⟩
   have hF (m:ℕ): a.S.block m=P.L (a.clock.J (m+1)):= by simpa only [hx.lengths] using a.fits.sameFactor m|>.symm
   constructor
   · intro m hm; rw [hF]; exact ((coded w).choose_spec k (a.clock.J (m+1)) (hN.trans (a.fits.mono (hm.trans (Nat.le_succ _))))).trans (h _)
   intro m hm; have hu:= (Hv Z hh).1 _ _ (hx.pays m) k (hN.trans (a.fits.mono (hm.trans (Nat.le_succ _)))) (a.clock.J m) (a.fits.mono (Nat.le_succ m))
   rw [← hF,postPay,dif_pos ⟨a.S.block_odd _,a.S.block_large _,a.clock.adm _,a.fits.mono (Nat.le_succ _),a.fits.stepSlow _⟩,←hx.stage] at hu
   exact hu
end buy

-- Power-of-three convention for later. independent of lengths list above.
lemma selects (s:Sheet G)(h:G.Simple): ∃ P:Rolls s,∀ i,∃ k:ℕ,(P.L i).val=3^k:= by
    open Finset in
    choose C hc using fun i=>Rolls.eventually_large s h i
    let W (i:ℕ):= (Finset.range (i+1)).sup C
    have hm : Monotone W:= fun i j hij=>Finset.sup_mono (Finset.range_mono (by omega))
    let v (i:ℕ):= (⟨3^W i, by positivity⟩:Side)
    have he (i:ℕ): C i ≤ (v i).val:= by
       have h (k:ℕ) : k < 3^k:= by
         induction k with | zero=> simp | succ k ih=> rw [pow_succ]; omega
       exact (Finset.le_sup (s:=Finset.range (i+1)) (f:=C) (Finset.mem_range.mpr (by omega))).trans (h (W i)).le
    have hX : Odd (3:ℕ):= ⟨1,rfl⟩
    exact ⟨⟨v,fun i=> hc _ _ (he i) hX.pow,fun i j hij=> pow_le_pow_right₀ (by decide) (hm hij)⟩,fun i=>⟨_,rfl⟩⟩
end YM.RG08.Admission
