import YM.RG08.Supplies.Caps
import YM.RG08.Reports.Receipt

/-!
# Assembly on the common witness and at any admitted step chain
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG08.Supplies
open Function Filter Lattice RG Tree Wilson Laurent Precision Pert.Bulk RG08.Flat RG08.Packets RG08.Line Stationary Bloch Matrix RG08.Rows RG08.Cell
open Function Set Filter MeasureTheory PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato Extraction Org Table Spec MergeProof
open UVExtension RG08
open scoped Classical Matrix Topology BigOperators ENNReal

variable {G:Gauge}{a:Levels G}
 set_option quotPrecheck false
local notation "ζ" => (Loc G 1) -- Quot parse?

private lemma hold_row {U : ℕ→ℕ→Kernel ζ ζ}{σ:ℕ→ℝ}{B c : ℝ}{r : ℕ}{Z:ℕ→ℝ}
    (hσ:∀i,0 < σ i)(hB:0≤B)(hZ:∀ k,0≤Z k)(hc:0<c)
    (S : Bool)(hp:Holders G a Z U S σ B r c) :
    ∃ F: ℕ→Kernel ζ ζ,∀ i,
      (∀ x y,Tendsto (fun N=> U N i x y) atTop (𝓝 (F i x y))) ∧
        ∀ k N,i<N → let s:=σ (a.clock.J (i+1)); let L:=a.S.block i; let q:= B*clock a.S Z k (i+1)^r*((a.S.a N/a.S.a (i+1))^c);
           RowCost (if S then s else s/L.val) (if S then L else 1) (U N i-F i) q ∧
           ColCost (if S then s else s/L.val) (if S then L else 1) (U N i-F i) q := by
  let X := fun (_:Market ζ × ζ)=>Cover
  let p i (z:Market ζ×ζ)(x:Cover):=let s:=σ (a.clock.J (i+1)); let L:=a.S.block i; (if S then s else s/L.val)*Pert.Bulk.delta (if S then L else 1) z.1.1 x
  let v i k N:= B*clock a.S Z k (i+1)^r*((a.S.a N/a.S.a (i+1))^c)
  let D i (N:ℕ):Sheet X ℝ:=fun z x=> U N i z.1 (x,z.2)
  have hA i k: Tendsto (v i k) atTop (𝓝 0) := by
    have h: Tendsto (fun n=>((a.S.a n/a.S.a (i+1))^c)) atTop (𝓝 0):= by
      simpa only [_root_.zero_div,Real.zero_rpow hc.ne'] using! (a.S.shrinks.div_const (a.S.a (i+1))).rpow (tendsto_const_nhds (x:=c)) (Or.inr hc)
    simpa only [v,mul_zero] using h.const_mul (B*clock a.S Z k (i+1)^r)
  have he i k N m (hi : i<N)(hn : N ≤ m):Ticket (p i) (fun z x=>D i N z x-D i m z x) (v i k N):= by
    have h:=hp.step i k N m hi hn
    cases S
    next =>
      simp only [Bool.false_eq_true,↓reduceIte] at h
      intro z; simpa only [X,D,p,v,stamp_real, earning,Pi.sub_apply,Bool.false_eq_true,↓reduceIte] using h.1 z.1 z.2 -- Pi.sub apply dsimp
    next =>
      simp only [↓reduceIte] at h
      intro z; simpa only [X,D,p,v,stamp_real,earning,Pi.sub_apply,↓reduceIte] using h.row z.1 z.2
  have hi i : ∃ F:Sheet X ℝ, ∀ z x,Tendsto (fun n=> D i n z x) atTop (𝓝 (F z x)):= by
    obtain ⟨F,h,-⟩ := stable (i+1) (K:=D i) (e:=p i) (fun x y=> by
      unfold p; apply mul_nonneg ?_ (Pert.Bulk.delta_nonneg ..); split <;> have hs:=hσ (a.clock.J (i+1)) <;> positivity) (hA i 0) (fun n m=> he i 0 n m) (fun n _=> by
        have hx:= a.S.a_pos n; have ht:=a.S.a_pos (i+1); unfold v clock; have hs:=hZ 0; positivity)
    exact ⟨F,h⟩
  choose F hF using hi
  let Y i : Kernel ζ ζ:=fun x y=> F i (x,y.2) y.1
  have heP (i)(x y:Market ζ): Tendsto (fun N=> U N i x y) atTop (𝓝 (Y i x y)):= hF i (x,y.2) y.1
  refine ⟨Y,fun i=> ⟨heP i,fun k N hN=>?_⟩⟩
  dsimp only
  let s1 := if S then σ (a.clock.J (i+1)) else σ (a.clock.J (i+1)) /(a.S.block i).val
  let L:= if S then a.S.block i else 1
  let D' (n:ℕ):Sheet X ℝ:=fun z y=> U n i (y,z.2) z.1
  constructor
  · intro x j
    have ht := ticket_of_limit (K:=fun n z y=> D i N z y-D i n z y) (T:=fun z y=>D i N z y-F i z y) (fun z y=>tendsto_const_nhds.sub (hF i z y)) ((eventually_ge_atTop N).mono fun n hn=> he i k N n hN hn)
    simpa only [v,Y,X,D,p, earning,stamp_real,Pi.sub_apply] using ht (x,j)
  intro j x
  have ht:=ticket_of_limit (K:=fun n z y=>D' N z y-D' n z y) (T:=fun z y=>D' N z y-Y i (y,z.2) z.1) (e:=fun z y=> s1*delta L y z.1.1) (p:=v i k N) (fun z y=> tendsto_const_nhds.sub (heP i (y,z.2) z.1)) ((eventually_ge_atTop N).mono fun n hn=> ?_)
  swap
  · have h := hp.step i k N n hN hn
    cases S with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at h
      intro z
      simpa only [earning, D', stamp_real, s1, L, v, Pi.sub_apply,
        Bool.false_eq_true, ↓reduceIte] using h.2.1 z.2 z.1
    | true =>
      simp only [↓reduceIte] at h
      intro z
      simpa only [earning, D', stamp_real, s1, L, v, Pi.sub_apply,
        ↓reduceIte] using h.col z.2 z.1
  simpa only [earning,s1,L,D',stamp_real,Pi.sub_apply] using ht (x,j)

variable (G) in
-- remove invalid var K
structure Pallet (K:KernelChoices)(a:Levels G)(H:Horizon a) (w:ℕ→ℝ)(B:ℝ)(r:ℕ)(c:ℝ): Prop where
  cap:0≤B
  decay:0<c
  usable i:0<w i
  fundsΓ:Holders G a (Lambda' a) (Sγ G a H) false w B r c
  fundsμ:Holders G a (Lambda' a) (Sμ G a H) true w B r c
  reports N i p (hi:i<N):let S:= a.clock.op i p; let b:=H.H N (i+1); let Γ:=NativeLine S G b;
    Matches (Sγ G a H N i) Γ ∧ Matches (Sμ G a H N i) (RootField K G S b) ∧
    (∀ x,onTree (green S) (Γ*ᵥ x)) ∧ (∀ x,onTree (green S) x → Γ*ᵥ(linePrecision G S b *ᵥ x)=x) ∧ Γ.transpose=Γ ∧
    RootField K G S b=patron G (extracted S (green S) (installed S.ratio (H.towers N i).A0))
  limits (s:Bool):let U:=if s then Sμ G a H else Sγ G a H
                  ∃ F: ℕ→Kernel ζ ζ,∀ i,(∀ x y,Tendsto (fun N=> U N i x y) atTop (𝓝 (F i x y))) ∧
                    ∀ k N,i<N → let L:=a.S.block i; let σ:=if s then w (a.clock.J (i+1)) else w (a.clock.J (i+1))/L.val; let L':=if s then L else 1; let q:= B*clock a.S (Lambda' a) k (i+1)^r*((a.S.a N/a.S.a (i+1))^c);
                      RowCost σ L' (U N i-F i) q ∧ ColCost σ L' (U N i-F i) q

lemma joined {H:Horizon a} {P X : MapPrices} {A B c : ℝ}{d l:ℕ}{F:ℕ→Kernel Links Links}
    (hk:G.Simple)(h:H.Suffices P) (hF:Quorum (curve X) F 0 H A B d l c)(hV:Available G a P): ∃ C r, Pallet G a.clock.kernel a H (Strip G P X a.clock.kernel) C r c:= by -- G explicit?
  obtain ⟨C,r,H₁,H₂,H₃,H₄⟩:= vessel hk h hF hV
  refine ⟨C,r,H₁,H₂,positive_strip,H₃,H₄,fun N i p hi=>?_,fun s=>?_⟩
  · let S:=a.clock.op i p; let j:=a.clock.J (i+1)
    let b:=H.H N (i+1)
    have hv:= (planSupply_spec G a.clock.kernel P j).2 (stone a i) (a.blocks i 0).branches rfl b (h.rows N (i+1) hi).2.1 (a.params (i+1)).clip (P.Ω j) (h.all N (i+1) hi)
    obtain ⟨hh,hε,hCη⟩:=plan_hr G a.clock.kernel P j
    obtain ⟨hN,hI⟩:= viewed hv hh.le hε S.sizes
    have ht:S=StepData.mk (stone a i) a.clock.kernel S.sizes := rfl
    -- h reports hN hI defeq S
    have ha : (a.S.side (i+1) p)= (a.S.side i p)*(stone a i).L:=Subtype.ext S.sizes
    have hη (n m:Side)(hv': m.val=n.val*(stone a i).L.val):let S:=(StepData.mk (stone a i) a.clock.kernel hv' : StepData n m); let M:=NativeLine S G b; (∀ x,onTree (green S) (M *ᵥ x))∧ (∀ x,onTree (green S) x→ M*ᵥ(linePrecision G S b*ᵥ x)=x) ∧ Mᵀ=M := by
      have ht:m=n*(stone a i).L:=Subtype.ext hv'; subst m; exact hv.invert n
    obtain ⟨Hz,Hx,HQ⟩:= hη _ _ S.sizes
    exact ⟨hN,hI,Hz,Hx,HQ,tree_station a.clock.kernel G rfl _ _ Hx (h.crossings N i p hi).trial⟩
  intro U
  have hZ k:0 ≤ Lambda' a k:=by unfold Lambda' Lambda; linarith [Real.log_pos (a.fits.delayed k)]
  cases s
  · exact hold_row positive_strip H₁ hZ H₂ false H₃
  exact hold_row positive_strip H₁ hZ H₂ true H₄
end YM.RG08.Supplies
