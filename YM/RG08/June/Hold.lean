import YM.RG08.Yamen.Rune
import YM.RG08.June.Arena
import YM.RG08.Aura.Publisher
import YM.Next.FOUNDATIONS.Primary
/-! # Common witness adapter all unmarked admissions (E ≤ J in use). Caller may
 announce arbitrary extra requirements in the SAME L/U degrees. Does NOT call sibling tasks.
 !-/
noncomputable section
namespace YM.RG08.June
open Yamen
open Lattice Laurent Pert.Bulk Forms Room Carrel Steam Isles Rows Rate Stair RG Stationary Bloch Rudder RG08.Mount Tack Anchor Spar Sedan Precision Finset Exterior Nacre PowerSeries Finset.Nat Symmetry Prism Quarry Roost Packets Ducat Mason
open Filter Flat PhysicalNext PhysicalNext.Repeat Extraction Org Table Spec UVExtension MergeProof
open scoped Classical Matrix BigOperators PowerSeries Topology
set_option autoImplicit false
variable {G:Gauge}

theorem holdem (G:Gauge)(hG:G.Simple)(Z:ChartRatio G)(hZ:LocalRatio Z)(k:RG.KernelChoices)(hk:∀ P:Patch,P.Branches k G)
    (N:Supply.Sheet G→MapPrices→MapPrices→ℕ→ℕ)(D:Supply.Sheet G→MapPrices→MapPrices→(ℕ→ℕ)→ℕ→ℝ):
    ∃ (C:Family G)(f:Extraction.Order)(T:YM.Table C.book)
        (F:Spec.Final C f T)(L:EveryPhase.Almanac F), C.Makes∧Spec.Calibrated C∧ C.path.levels.clock.kernel=k∧ UVExtension.Oasis.Floral (hG:=hG) C∧ (Extraction.Order.mk Extraction.Sequence.full f.per).Ordered C T∧ (∀ d u:ℕ, ∀ᶠ n:ℕ in atTop,∀ (r:ℕ)(v:Fin r→ C.book.Token),(∀ i,(v i).1≤ d)→∃ g,Poppy.Margins C r n u v g)∧EveryPhase.Completed F L ∧∃ (s:Supply.Sheet G)(P X:MapPrices)(H:Horizon C.path.levels), C.path.levels.clock.kernel = s.kernel ∧ C.path.levels.clock.stage = s.profile ∧
      Legato.ExtraGates (fun s p=>N s p X) (fun s p=>D s p X) C s P H ∧ Aura.licensed C.path.levels H ∧ Scheme C H (Case.actualPay s P) X Z:=by -- Legato namespace Reports.ExtraGates
 have h (s:Supply.Sheet G) := entrance_gate hG s.kernel s rfl
 choose X E Hx using h
 choose Y HY using fun s:Supply.Sheet G=> Cast.assured G s.kernel s rfl
 choose Lic Hl using Aura.dual_support G
 let n(s:Supply.Sheet G)(p:MapPrices)(i:ℕ):=max (max (E s i) (Y s i)) (max (max (Lic s i) (N s p (X s) i)) (Yamen.need G (Case.actualPay s p) (X s) s.kernel i))
 let d(s:Supply.Sheet G)(p:MapPrices)(v:ℕ→ℕ)(i:ℕ):= max (D s p (X s) v i) (Yamen.shade G (Case.actualPay s p) (X s) s.kernel Z v i)
 obtain ⟨C,f,T,F,L,hF,hT,hκ,hs,hA,hd,hP,s,p,H,hg⟩:=Reports.paid hG k hk n d
 let a:=C.path.levels
 have hN (m:ℕ):let i:=a.clock.J (m+1);n s p i ≤ (a.S.block m).val:=by rw [←a.fits.sameFactor];exact hg.cluster _
 have hB:Bill G (Case.actualPay s p) (X s) a:=fun i=> le_trans (le_max_right ..) ((le_max_right ..).trans (by
       unfold a;rw [hg.kernel];exact hg.cluster i)) -- def rewriting Case need includes s vs C; apply differently
 have hu:Payment G (Case.actualPay s p) (X s) Z a:=fun i=> by unfold a; rw [hg.kernel]; exact le_trans (le_max_right ..) (hg.payment i)
 have hD : Flat.Delay a (X s) 0:=by
    intro i _
    have he:=hatch hu i
    exact ((stamped G _ _ a.clock.kernel _ (RG08.Supplies.stone a i)).arms (a.clock.J i) (a.fits.mono (by omega:i ≤ i+1))).trans he
 obtain ⟨U,A,B,b,c,M,h⟩:=Hx s a hg.kernel hg.profile (fun m=> le_trans (le_max_left ..) ((le_max_left ..).trans (hN m))) 0 hD
 let W:= Case.actualPay s p
 refine ⟨C,f,T,F,L,hF,hT,hκ,hs,hA,hd,hP,s,p,X s,H,hg.kernel,hg.profile,?_,Hl s a hg.kernel hg.profile (fun m=>le_trans (le_max_left ..) ((le_max_left ..).trans ((le_max_right ..).trans (hN m)))) H hg.atlas,⟨⟨hg.atlas,fun N i c hi=>HY s a hg.kernel hg.profile (fun m=>le_trans (le_max_right ..) ((le_max_left ..).trans (hN m))) H hg.atlas _ _ _ hi,hZ⟩,hg.attached,hu,hB,U,A,B,M,b,c,h H W hg.atlas⟩⟩
 exact { hg with cluster := fun i=> le_trans (le_max_right ..) ((le_max_left ..).trans ((le_max_right ..).trans (hg.cluster i))), payment := fun i=> le_trans (le_max_left ..) (hg.payment i) } -- dependent inherited via extends? field names
end YM.RG08.June
