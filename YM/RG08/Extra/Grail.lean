import YM.RG08.Extra.Spill
/-!
 # Analytic extras behind Ribbon.

 Pre width price before L. Uses NO tape contact assumptions. Same loopCap
 e.g. can be `loopCap i`, charge occurs in RENDER ONLY ($pgeo$) as aligned
 analytic extras behind base; it is not part of preceding $Age$ budget
 for coarser recurrence. One who uses stronger caps may pass them instead.
 `Invoice pays` asks NORMALIZED kernels compiled at all tested mesh side
 c. No masks; no implied response of a held-field in force. Higher q≥2
 use `boat` in Wilson (reference=0). For E≤1 needn't ask for these bills.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG08.Spills
open Filter MeasureTheory YM.PertExtension.Series.Tested
open Function Analysis Tree Lattice RG Stationary Wilson Precision Exterior Laurent Finset Next.Free Matrix FreeResolvent Reflect Bloch UVExt.Paths Conductor Virtue Staffer Canon
open PertExtension.Series.Radial PertExtension.Chart PertExtension.GaussianScore
open scoped BigOperators Topology Real ContDiff Classical Matrix.Norms.Frobenius
variable {G:Gauge}{P Q:Atlas G}{p:Clip}{σ C A B Λ D τ w : ℝ}
lemma quote (G:Gauge) (d:ℕ) (X:RG.Stage) (Z:ℝ) (hp:0<Z) :
   ∃ w C : ℝ,0<w ∧ 0≤C ∧ ∀ (U:Air G)(F:Pot G 2)(R:PathData G)(Γ A:ℝ),0≤ Γ→0≤ A→(∀ m, Cask X.clip R m F U)→
       Gets U → Tunable F→ R.Bounds X.clip X.width X.paths Γ → (∀ e r, (q:r≤d+4) → e≤d+2 → Glow (U e r) Z A) →
       (∀ m,Faithful F U m) → ∃ T V:Flotilla G,
           Invoice (fun m=> classicFn X.clip R (f:=m)) (sector F U 0) 3 d w ((1+A)*C) T ∧
           Invoice (fun m=> loopFn R (f:=m)) (sector F U 1) 1 d w ((1+A+Γ)*C) V := by
  obtain ⟨u,K,hU,hK,H⟩:= all_pre G (3+d) X.clip X.paths X.width_pos X.paths_pos.le
  obtain ⟨x,B,hx,hB,H'⟩:= retrofit G 3 d (by decide) (lt_min hU hp)
  obtain ⟨y,D,hy,hD,X'⟩:= retrofit G 1 d (by decide) (lt_min hU hp)
  let C:=(1+K)*(B+D)
  refine ⟨min x y,C, lt_min hx hy, by unfold C; positivity, fun U F R Γ A hg ha hR ht hF hh hE Hs=>?_⟩
  have he (q j):= Tune_sector U F (fun i j=>(ht.2 i j).1) hF q j
  obtain ⟨T,hT⟩:=H' (fun m=> classicFn X.clip R (f:=m)) A K (sector F U 0) (fun i hi=> Foil.mono ((H R _ hh (i+1) (by simp only [embark,mem_Ico] at *; omega)).1) (lt_min hU hp) (min_le_left ..) le_rfl) ha hK (fun j hj=> by simp only [embark,mem_Ico] at hj; rw [sector_unique F U (e:=j) (by omega) (by omega) (by omega)]; exact glow_less (hE _ _ (by omega) (by omega)) (min_le_right ..) le_rfl) (he 0) (fun m=>⟨strain X.clip R hh,(hR m).bound⟩) (fun m=>Hs m 0 _)
  obtain ⟨V,hV⟩ := X' (fun m=> loopFn R (f:=m)) A (Γ*K) (sector F U 1) (fun i hi=>Foil.mono ((H R _ hh (i+1) (by simp only [embark,mem_Ico] at *; omega)).2) (lt_min hU hp) (min_le_left ..) le_rfl) ha (mul_nonneg hg hK) (fun i hi=> by simp only [embark,mem_Ico] at hi; rw [sector_unique F U (e:=i+2) (by omega) (by omega) (by omega)]; exact glow_less (hE _ _ (by omega) (by omega)) (min_le_right ..) le_rfl) (he 1) (fun m=> ⟨stain_ink _ hh.width hh.two (fun i=>(hh.invariant i).1),(hR m).ropes⟩) (fun m=>Hs m 1 _)
  have hb : B+D ≥ 0 := add_nonneg hB hD
  refine ⟨T,V,⟨fun i hi=>(hT.1 i hi).mono ?_ (min_le_left ..),hT.2⟩,⟨fun i hi=>(hV.1 i hi).mono ?_ (min_le_right ..),hV.2⟩⟩
  · unfold C; rw [← mul_assoc]; gcongr; nlinarith; exact le_add_of_nonneg_right hD
  unfold C; rw [← mul_assoc]; gcongr; nlinarith; exact le_add_of_nonneg_left hB
-- provide exact orientation-∞ books to consumer, field rank <=4/d+etc.
structure Reserves (ν : G.ColorIndex){H:Levels G} {D:ChartRatio G}{s:Supply.Sheet G}{M:Supply.Rolls s}{P:PostCost M} {Y:Horizon H}{U:Kin Y D}(F:Kin.Planned U P)(w:ℕ→ℝ)(n:ℕ) where
    tariff : ℕ→ℝ
    venue : ℕ→ℝ
    hp i : 0≤ tariff i
    hT i : 0< venue i
    pays (N i:ℕ)(hh : i≤N) : G.Simple → LocalRatio D→let a := (Chain.actual H)
        let R:= U.path N i; let Ω:= H.params i
        let b:= H.clock.J i; let V:= a.album ν D N i; let B := Chain.column G a N i
        ∀ A:ℝ,0≤A → (∀ e r,r≤n+4 → e≤ n+2 → Glow (V e r) (w b) A) → ∃ X Y,
           Invoice (fun m=> classicFn Ω.clip R (f:=m)) (sector B V 0) 3 n (venue b) ((1+A)*tariff b) X ∧
           Invoice (fun m=> loopFn R (f:=m)) (sector B V 1) 1 n (venue b) ((1+A+H.clock.loopCap i)*tariff b) Y

-- actually pre warranty: tied to already supplied Levels (e.g actual Floral); quotes universal.
lemma extra_serve (ν : G.ColorIndex){H:Levels G} {D:ChartRatio G}{s:Supply.Sheet G}{M:Supply.Rolls s}{P:PostCost M} {Y:Horizon H}{U:Kin Y D}(F:Kin.Planned U P)(w:ℕ→ℝ)(n:ℕ)(hp:∀ i,0<w i) : Nonempty (Reserves ν F w n) := by
  choose b C hB hC H' using fun i=> quote G n (H.clock.stage i) (w i) (hp i)
  let a:= Chain.actual H; have hx:= Chain.wake_actual H
  refine ⟨⟨C,b,hC,hB,fun N i hh hG hD=>?_⟩⟩
  obtain ⟨he,hP,hX⟩:= a.high_stocks ν N i
  have HV := a.packing ν D hx hD hh
  intro a' R Ω Z V A B hk HZ
  refine H' (H.clock.J i) _ _ _ _ _ ?_ hk (fun m=> rides (F.cap N i hh) (planned_pay F ν hG hD N i hh) (Chain.side_infinite H.S i) he hP HV.gets m) HV.gets he (F.cap _ _ hh) HZ HV.opens
  unfold Calendar.loopCap Calendar.monitor; positivity
end YM.RG08.Spills
