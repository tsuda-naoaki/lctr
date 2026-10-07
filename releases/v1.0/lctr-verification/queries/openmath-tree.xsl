<?xml version="1.0"?>
<xsl:stylesheet version="1.0" xmlns:xsl="http://www.w3.org/1999/XSL/Transform" xmlns:o="http://www.openmath.org/OpenMath" exclude-result-prefixes="o">
  <xsl:output method="xml" omit-xml-declaration="yes"/>
  <xsl:strip-space elements="*"/>
  <xsl:template match="o:OMOBJ"><xsl:apply-templates/></xsl:template>
  <xsl:template match="o:OMV"><var name="{@name}"/></xsl:template>
  <xsl:template match="o:OMA"><app name="{o:OMS[1]/@cd}.{o:OMS[1]/@name}"><xsl:apply-templates select="*[position() &gt; 1]"/></app></xsl:template>
  <xsl:template match="o:OMBIND"><bind name="{o:OMS[1]/@cd}.{o:OMS[1]/@name}"><xsl:apply-templates select="*[position() &gt; 1]"/></bind></xsl:template>
  <xsl:template match="o:OMBVAR"><vars><xsl:apply-templates/></vars></xsl:template>
  <xsl:template match="*"><xsl:message terminate="yes">Unsupported OpenMath element</xsl:message></xsl:template>
</xsl:stylesheet>
