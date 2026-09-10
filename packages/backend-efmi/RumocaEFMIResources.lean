import Std

/-! The complete schema-resource roster from the pinned eFMI 1.0.0 Beta 1
release. `efmiSchemas` is this library's Lake input-directory dependency;
its binary trace preserves changes to line endings. `include_str` embeds the
actual resource contents as Lean string literals. No runtime file lookup or
producer-supplied checksum inventory defines the required archive resources.
The upstream BSD license is included as a member. -/
namespace Rumoca.EFMI.Resources

structure Resource where
  name : String
  text : String

def schemas : List Resource := [
  Resource.mk "schemas/AlgorithmCode/VERSION.txt" (include_str "vendor/efmi/schemas/AlgorithmCode/VERSION.txt"),
  Resource.mk "schemas/AlgorithmCode/efmiAlgorithmCodeManifest.xsd" (include_str "vendor/efmi/schemas/AlgorithmCode/efmiAlgorithmCodeManifest.xsd"),
  Resource.mk "schemas/AlgorithmCode/efmiVariable.xsd" (include_str "vendor/efmi/schemas/AlgorithmCode/efmiVariable.xsd"),
  Resource.mk "schemas/BehavioralModel/VERSION.txt" (include_str "vendor/efmi/schemas/BehavioralModel/VERSION.txt"),
  Resource.mk "schemas/BehavioralModel/efmiBehavioralModelManifest.xsd" (include_str "vendor/efmi/schemas/BehavioralModel/efmiBehavioralModelManifest.xsd"),
  Resource.mk "schemas/BehavioralModel/efmiClocks.xsd" (include_str "vendor/efmi/schemas/BehavioralModel/efmiClocks.xsd"),
  Resource.mk "schemas/BehavioralModel/efmiCsvMappings.xsd" (include_str "vendor/efmi/schemas/BehavioralModel/efmiCsvMappings.xsd"),
  Resource.mk "schemas/BehavioralModel/efmiScenarios.xsd" (include_str "vendor/efmi/schemas/BehavioralModel/efmiScenarios.xsd"),
  Resource.mk "schemas/BehavioralModel/efmiTolerancesSetups.xsd" (include_str "vendor/efmi/schemas/BehavioralModel/efmiTolerancesSetups.xsd"),
  Resource.mk "schemas/BehavioralModel/efmiVariables.xsd" (include_str "vendor/efmi/schemas/BehavioralModel/efmiVariables.xsd"),
  Resource.mk "schemas/BinaryCode/VERSION.txt" (include_str "vendor/efmi/schemas/BinaryCode/VERSION.txt"),
  Resource.mk "schemas/BinaryCode/efmiBinaryCodeManifest.xsd" (include_str "vendor/efmi/schemas/BinaryCode/efmiBinaryCodeManifest.xsd"),
  Resource.mk "schemas/BinaryCode/efmiBinaryContainerInfoFileReferences.xsd" (include_str "vendor/efmi/schemas/BinaryCode/efmiBinaryContainerInfoFileReferences.xsd"),
  Resource.mk "schemas/BinaryCode/efmiBuildInformation.xsd" (include_str "vendor/efmi/schemas/BinaryCode/efmiBuildInformation.xsd"),
  Resource.mk "schemas/BinaryCode/efmiModules.xsd" (include_str "vendor/efmi/schemas/BinaryCode/efmiModules.xsd"),
  Resource.mk "schemas/BinaryCode/efmiObjectFile.xsd" (include_str "vendor/efmi/schemas/BinaryCode/efmiObjectFile.xsd"),
  Resource.mk "schemas/BinaryCode/efmiRunTimeComplianceInformation.xsd" (include_str "vendor/efmi/schemas/BinaryCode/efmiRunTimeComplianceInformation.xsd"),
  Resource.mk "schemas/LICENSE" (include_str "vendor/efmi/schemas/LICENSE"),
  Resource.mk "schemas/ProductionCode/VERSION.txt" (include_str "vendor/efmi/schemas/ProductionCode/VERSION.txt"),
  Resource.mk "schemas/ProductionCode/efmiCodeFiles.xsd" (include_str "vendor/efmi/schemas/ProductionCode/efmiCodeFiles.xsd"),
  Resource.mk "schemas/ProductionCode/efmiDimensions.xsd" (include_str "vendor/efmi/schemas/ProductionCode/efmiDimensions.xsd"),
  Resource.mk "schemas/ProductionCode/efmiFunctions.xsd" (include_str "vendor/efmi/schemas/ProductionCode/efmiFunctions.xsd"),
  Resource.mk "schemas/ProductionCode/efmiIncludes.xsd" (include_str "vendor/efmi/schemas/ProductionCode/efmiIncludes.xsd"),
  Resource.mk "schemas/ProductionCode/efmiLogicalData.xsd" (include_str "vendor/efmi/schemas/ProductionCode/efmiLogicalData.xsd"),
  Resource.mk "schemas/ProductionCode/efmiMacros.xsd" (include_str "vendor/efmi/schemas/ProductionCode/efmiMacros.xsd"),
  Resource.mk "schemas/ProductionCode/efmiProductionCodeManifest.xsd" (include_str "vendor/efmi/schemas/ProductionCode/efmiProductionCodeManifest.xsd"),
  Resource.mk "schemas/ProductionCode/efmiSupportedLanguages.xsd" (include_str "vendor/efmi/schemas/ProductionCode/efmiSupportedLanguages.xsd"),
  Resource.mk "schemas/ProductionCode/efmiSupportedPlatforms.xsd" (include_str "vendor/efmi/schemas/ProductionCode/efmiSupportedPlatforms.xsd"),
  Resource.mk "schemas/ProductionCode/efmiTargetTypes.xsd" (include_str "vendor/efmi/schemas/ProductionCode/efmiTargetTypes.xsd"),
  Resource.mk "schemas/ProductionCode/efmiTechnicalLookUps.xsd" (include_str "vendor/efmi/schemas/ProductionCode/efmiTechnicalLookUps.xsd"),
  Resource.mk "schemas/ProductionCode/efmiTypeDefs.xsd" (include_str "vendor/efmi/schemas/ProductionCode/efmiTypeDefs.xsd"),
  Resource.mk "schemas/ProductionCode/efmiVariables.xsd" (include_str "vendor/efmi/schemas/ProductionCode/efmiVariables.xsd"),
  Resource.mk "schemas/VERSION.txt" (include_str "vendor/efmi/schemas/VERSION.txt"),
  Resource.mk "schemas/efmiAnnotation.xsd" (include_str "vendor/efmi/schemas/efmiAnnotation.xsd"),
  Resource.mk "schemas/efmiCompilerOptions.xsd" (include_str "vendor/efmi/schemas/efmiCompilerOptions.xsd"),
  Resource.mk "schemas/efmiContainerManifest.xsd" (include_str "vendor/efmi/schemas/efmiContainerManifest.xsd"),
  Resource.mk "schemas/efmiFiles.xsd" (include_str "vendor/efmi/schemas/efmiFiles.xsd"),
  Resource.mk "schemas/efmiFloatingPointPrecision.xsd" (include_str "vendor/efmi/schemas/efmiFloatingPointPrecision.xsd"),
  Resource.mk "schemas/efmiIdentifierType.xsd" (include_str "vendor/efmi/schemas/efmiIdentifierType.xsd"),
  Resource.mk "schemas/efmiLinkerOptions.xsd" (include_str "vendor/efmi/schemas/efmiLinkerOptions.xsd"),
  Resource.mk "schemas/efmiManifestAttributes.xsd" (include_str "vendor/efmi/schemas/efmiManifestAttributes.xsd"),
  Resource.mk "schemas/efmiManifestReferences.xsd" (include_str "vendor/efmi/schemas/efmiManifestReferences.xsd"),
  Resource.mk "schemas/efmiModelRepresentationKind.xsd" (include_str "vendor/efmi/schemas/efmiModelRepresentationKind.xsd"),
  Resource.mk "schemas/efmiUnits.xsd" (include_str "vendor/efmi/schemas/efmiUnits.xsd"),
  Resource.mk "schemas/efmiWildcard.xsd" (include_str "vendor/efmi/schemas/efmiWildcard.xsd")]

end Rumoca.EFMI.Resources
