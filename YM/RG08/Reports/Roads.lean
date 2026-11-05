import YM.UVExtension.Reports.Ultraviolet
import YM.EveryPhase.Extension
/-!
# Adapter offering the UV/every-phase witness with compatible extra calendar gates

One may need to add stage restrictions before L and requests for delays after L. `with_asks` proof
is adapted from Legato.uv_flowered (in UVExtension/Oasis/Hall.lean, accepted seed); uses the
same uv_wishes provider but now sends the extra asks and retains the same `A.B` linear plan and
gate payments on the *actual* Family. Does not choose or modify any branch of arc/germ estimates.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Legato
open Function Filter Set Lattice RG RG.Shoot Wilson Precision RG.Supply Input Org Extra.Histories Source
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext
open WilsonStartup Progress.DirectedRecipe Time Next.Foundations UVNext.CouplingReset
open Cub Circlet Graces Roost Planned.GuardedAtom Bandage
open InteractingRank Next.Rank Next.Rank.Tapes RankCovariance PhysicalNext.InteractingRank.Soft
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G:Gauge}
open Next.Extract Dash
open YM.MergeProof MergeProof.Accent
open UVExtension UVExtension.Harvest

structure ExtraGates
    (needs : Supply.Sheet G → MapPrices → ℕ → ℕ)
    (delay : Supply.Sheet G → MapPrices → (ℕ→ℕ) → ℕ → ℝ)
    (C : Family G) (s : Supply.Sheet G) (price : MapPrices) (H : Horizon C.path.levels) : Prop where
  kernel : C.path.levels.clock.kernel=s.kernel
  profile : C.path.levels.clock.stage=s.profile
  atlas : H.Suffices (Case.actualPay s price)
  cluster i : needs s price i ≤ (C.path.levels.clock.factor i).val
  payment m : delay s price (fun i=> (C.path.levels.clock.factor i).val) (C.path.levels.clock.J (m+1)) ≤ C.path.levels.clock.hatBeta m
  attached N i p : i≤N →
    let H':=C.path
    Attached (H.H N i) (H'.rep N p i).path

theorem with_asks (hG:G.Simple)(k:KernelChoices)(hp:∀ p:Patch,p.Branches k G)
    (needs : Supply.Sheet G → MapPrices → ℕ → ℕ)
    (delay : Supply.Sheet G → MapPrices → (ℕ→ℕ) → ℕ → ℝ) :
    ∃ C:Family G, C.path.levels.clock.kernel=k ∧ Spec.Calibrated C ∧ C.Makes ∧ Extraction.Wcmain C ∧
    UVExtension.Oasis.Floral (hG:=hG) C ∧ Acme.Aroma C ∧ (∀ F:Extraction.Order, Cells.CellHyp C F → Grill C F∧MergeProof.East.CompleteWeak C F)∧(∀ f:Extraction.Order, ∃ (g:Extraction.Order) (A:Table C.book) (L:ℕ→Table C.book) (R:Bin A) (T:Table C.book) (E:DiffPlan T), Next.Extract.Base C (f.refine g) A L R T E ∧ ∃ s:Spec.Seed C (f.refine g) T,Maxwell.Ranks T s.kernel.spin) ∧ ∃ s price H,ExtraGates needs delay C s price H := by
  let v: Orders:= ⟨4,fun i=>6+i,fun i=>2+i,fun i=>100+i⟩
  have hE (i:ℕ): 100 ≤ v.supportExp i:= by change (100:ℝ) ≤ 100+i; simp
  have he : Draft v:= by
    refine ⟨le_rfl,fun i j hij=> Nat.add_le_add_left hij 6,fun i j hij=> Nat.add_le_add_left hij 2,fun i j hij=>?_,fun i=> lt_of_lt_of_le (by norm_num) (hE i),fun i=>by change _ ≤6+i; omega,fun i=>by change _≤2+i; omega⟩
    change (100:ℝ)+i≤100+j; gcongr
  obtain ⟨s,PV,Y,K,hX,H,l,hL,hK⟩:= uv_wishes hG hp he (fun _=>1) (fun _ _ _=>le_rfl) (fun _=>le_rfl) hE
  let M:=UVExtension.Case.provider s PV (l ⊔ (needs s PV))
  obtain ⟨⟨P⟩,H⟩:= hK (l ⊔ (needs s PV)) le_sup_left
  let Q (i j:ℕ): JointLoad.Clockwork.Menu:= ⟨Push.SectorMeasure.Chi.canonical,1,0,0,0,0,0,0,one_pos,le_rfl⟩
  let J₀ (i j:ℕ):JointLoad.Folio.Aux:=⟨40,1,1,le_rfl⟩
  let E : Next.Scheduling.Exchange:=⟨0,0,1,1,1,0,0,by norm_num⟩
  obtain ⟨w,h⟩:= H P
  obtain ⟨F,hF⟩:= h w le_rfl (fun _ _=> ⟨1,1,1,1,le_rfl,zero_lt_one,zero_lt_one⟩) (fun _ _=> E)
  obtain ⟨θ,-,hH⟩:= hF _ (fun _=>one_pos)
  let U: Delays θ:=⟨delay s PV (fun i=> (P.L i).val) ,fun _ _=>0,fun _=>1,fun _=>1⟩; obtain ⟨V,h₁,hK⟩:= hH Q J₀ U
  obtain ⟨D,-⟩:= Bar.exists_above V 2; let I:Wait D:= ⟨fun _=>0,fun _ _=>0,fun _=>by simp,0⟩
  obtain ⟨Y,-,H⟩:= hK V (DelayLe.refl _) D I
  obtain ⟨a,ha,hp⟩:= Wait.engine Y hG; obtain ⟨X,B,hB,R,W,c,T,t,S,Hx,Hk,hT,hq,hu,hD,h_lease,h_rate,⟨hh',hH,h_Φ,h_sh⟩,hE⟩:= H Y le_rfl le_rfl le_rfl a ha hp
  let V:= Mast.centerB S Hx; let W:=Mast.cellar S c Hx t Hk; let S':= Mast.Cellar.gate (Mast.roseA S) W
  let Z:= Family.mk (Issue.trail V) (hol G) (Labels.frames G) (localSection G) t S'
  obtain ⟨hc,hF,hQ,hU,hW,B₀,-,-,K₀,F₀,L,-,H⟩:=hT.reception
  have hv:Ribbons.Created Z:= ⟨_,t,S',rfl⟩
  have hπ:Acme.Aroma Z:= ⟨Ribbons.laurelE Z hG hU hu hq hv hF,hq, Ribbons.fugacious Z hG hu⟩
  have extra : ExtraGates needs delay Z s PV B.M := by
    refine ⟨B.valid.kernel,B.valid.stage,B.plan,fun i=>?_,fun m=>?_,fun N i p ht=>?_⟩
    · have hv := (P.large i).need
      change _ ≤ (B.a.clock.factor _).val
      rw [B.valid.lengths]
      exact (le_sup_right (a:=l) (b:=needs s PV) i).trans hv
    · change delay s PV (fun i=>(B.a.clock.factor i).val) _ ≤ B.a.clock.hatBeta m
      rw [B.valid.lengths]
      let stage:=B.a.clock.J (m+1)
      have hh : delay s PV (fun i=>(P.L i).val) stage ≤ _ := h₁.beta stage
      exact hh.trans (B.valid.pays m)
    · have hh : (V.history N p i).path=B.kin.path N i := by rw [← B.bases]; exact ((V.sticks N p).prices i (Nat.zero_le _) ht).1.path
      change Attached (B.M.H N i) (V.history N p i).path
      rw [hh]; exact B.support.links N i ht
  exact ⟨_,B.valid.kernel.trans hX,hc,hF,hW,Oasis.survives W Hx hD hQ hh' hH (hB.symm ▸ h_Φ) h_sh h_lease h_rate hT hu, hπ, (fun f hf=>⟨grilled Z hF hU hq hf,hE f⟩), (fun f=>by obtain ⟨g,A,L,R,z,T,E,h,hp⟩:= H f; exact ⟨g,A,L,R,T,E,hp⟩),_,_,_,extra⟩
end YM.PhysicalNext.Repeat.Legato
